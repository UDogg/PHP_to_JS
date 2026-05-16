<?php

namespace App\Http\Controllers;

use App\Events\userCreation;
use App\Http\Requests\UserBankDetailsReq;
use App\Models\QualificationMaster;
use App\Models\Role;
use App\Models\SellNow;
use App\Models\User;
use App\Models\UserMapping;
use App\Models\userTypes;
use App\Models\ZoneMasterModel;
use Carbon\Carbon;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;
use App\Models\UserAccessManagment;
use App\Services\UserService;
use App\Models\EmailActivityLog;

use App\Models\SSO;
use App\Models\TokenModel;
class UserControllerNew extends Controller
{
    protected $authenticatedUser;
    protected $userRoleMapping;
    protected $UserlobMapping;
    protected $userService;
    public function __construct(Auth $auth, RolesController $rolecontroller, SellNowController $sellNowController,UserService $userService)
    {
        $this->authenticatedUser = $auth::user();
        $this->userRoleMapping = $rolecontroller;
        $this->UserlobMapping  = $sellNowController;
        $this->userService = $userService;
    }

    public function UserBankDetails(UserBankDetailsReq $request, int $id)
    {

        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (!$this->authenticatedUser->can($permission)) {

            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $user = User::find($id);
        $user->bank_name = credential_encrypt($request->bank_name);
        $user->bank_city = credential_encrypt($request->bank_city);
        $user->account_no = credential_encrypt($request->account_no);
        $user->ifsc_code = credential_encrypt($request->ifsc_code);
        $user->bank_branch = credential_encrypt($request->branch);
        $user->account_holder_name = credential_encrypt($request->account_holder_name);
        $user->save();
        $userId = $user->id;
        if ($user) {

            return  requestResponseMessage(['status' => 200, 'message' => 'User Updated Successfully', 'data' => [
                'email' => $request->email,
                'userId' => $userId
            ]]);
        } else {
            return  requestResponseMessage(['status' => 403, 'message' => 'Error While Updating User.']);
        }
    }

    protected function getPosReportingEmployeeCode($employeeId)
    {
        $EnsuringEmployeeUser = userTypes::select('id')->where('Identifier', 'E')->first()['id'];
        $reportingEmployeeCode = User::select('employee_code')->where('id', $employeeId)->where('usertype', $EnsuringEmployeeUser)->first()['employee_code'] ?? 0;
        return $reportingEmployeeCode;
    }
    public function store(Request $request)
    {
        $authenticatedUser = $this->authenticatedUser;
        $employe_code_of_current_user = $authenticatedUser->employee_code;

        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
  
        if (!$authenticatedUser->can($permission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $AllowMultipleUsers = config('Broker.Allow.Multiple.users');
        $defaultPartnerUserForPosp = config("Broker.Default.Partner");

        $rules = [
            // 'username' => 'required|string',
            'name' => 'required|string',
            // 'middle_name' => 'required|string',
            // 'last_name' => 'required|string',
            'mobile' => 'required|regex:/^[0-9]{10}$/',
            'email' => 'required|email',
            // 'gender' => 'required|string|in:M,F',
            // 'address' => 'required|string',
            // 'pincode' => 'required|digits:6',
            'status' => 'required|in:N,Y',
            'user_type' => 'required|integer',
            'role_id' => 'required|integer',
            'lob_id' => 'required|array',
            // 'qualification' => 'required|integer',
            // 'dob' => 'required|date_format:d/m/Y',
            // 'reportingRole' => 'required|integer',
            // 'reportingTo' => 'required|integer'
            
        ];

        $role_reporting_to = Role::where('id', $request->role_id)->pluck('reporting_role')->first();

        if ($role_reporting_to !== 0) {
            $rules['reportingRole'] = 'required|integer';
            $rules['reportingTo'] = 'required|integer';
        }


        $getusertype = userTypes::select('name', 'Identifier')->where('id', $request->user_type)->where('is_active', 'Y')->first();
        if ($getusertype->Identifier == 'MISP') {
            $rules['oemId'] = 'required|integer';
            $rules['mispId'] = 'required|integer';
            $rules['branchId'] = 'required|integer';
        }
        $userCode = '';
        $reportingEmployeeCode = null;
        if ($getusertype->Identifier == 'E' || $getusertype->Identifier == 'SP') {
            $validate = $request->validate([
                'employeeCode' => 'required|string',
            ]);
            if (User::where('employee_code', $request->employeeCode)->exists()) {
                return response()->json(['message' => 'The employee code already exists.'], 400);
            }
            $reportingEmployeeCode = $request->employeeCode;
        }
        if ($getusertype->Identifier == 'P') {
            $validate = $request->validate([
                'posCode' => 'required|string',
                'license_start_date' => 'required|date_format:d/m/Y',
                'license_end_date' => 'required|date_format:d/m/Y',
                'adhar_no' => 'required|digits:12',
                'pan_no' => 'required|regex:/^[A-Z]{5}[0-9]{4}[A-Z]$/'
            ]);
            $userCode = $request->posCode;

            $reportingEmployeeCode = User::select('employee_code')->where('id', $request->reportingTo)->first()['employee_code'] ?? 0;
            // $reportingEmployeeCode = $employe_code_of_current_user ?? 0;
            $reportingUser = User::select('employee_code', 'usertype')->where('id', $request->reportingTo)->first();

            // If reporting user's usertype = 2 then employee_code = null
            if ($reportingUser && $reportingUser->usertype == 2) {
                $reportingEmployeeCode = null;
            } else {
                $reportingEmployeeCode = $reportingUser->employee_code ?? 0;
            }

        }
        if ($getusertype->Identifier == 'Partner') {
            
            $reportingUser = User::where('id', $request->reportingTo)->first();
            if ($reportingUser && (int)$reportingUser->usertype == 3) {
                $reportingEmployeeCode = null;
            } else {
                $reportingEmployeeCode = $reportingUser->employee_code ?? User::where('id', 2)->value('employee_code');
            }

        }
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()], 400);
        }
 
        $reportingRoleUsertype = Role::where('id',$request->reportingRole)->pluck('user_type')->first();

        $check_mail = User::select('email', 'id','usertype')->where('mobile', credential_encrypt($request->mobile))->first();
        $userexist =  User::where('email',credential_encrypt($request->email))->first();

        if ($check_mail && $check_mail->usertype == $request->user_type || !is_null($userexist)) {
            return response()->json(['message' => 'User already exists.'], 400);
        }
        if ($check_mail) {

            if($AllowMultipleUsers == 'Y' ||( $defaultPartnerUserForPosp == 'Y' && $getusertype->Identifier == 'P'))
            {
                if ($request->user_type == 1) {
                    return $this->prepareUserData($request->all(),$reportingEmployeeCode,$check_mail);
                }else { 
                    $this->UserMapUsertype($check_mail->id,$request->user_type,$request->role_id,$request->reportingTo,$reportingEmployeeCode);
                    return  response()->json([
                        'status' => 200,
                        'message' => 'User Created Mapping Successfully'
                    ]);
                }
            }
            else
            {
                return requestResponseMessage(['status' => 500, 'message' => 'User  Already Exists please Try with other email username and mobile number']);
            }       
        } 
            DB::beginTransaction();
            try {
                $qrCode_generated = generateQrcode();
                $secret = $qrCode_generated['secret'];
                $totp_secret = credential_encrypt($secret);

                if (config('random-pass') == 1) {
                    $password = generateRandomPassword(8);
                } else {
                    $password = "Admin@123";
                }
                $userName = config('fetch_sp_details') ? credential_encrypt($request->employeeCode) : credential_encrypt($request->mobile);

                $inserted = User::updateOrCreate([
                    'username' => $userName,
                    'name'     => credential_encrypt($request->name),
                    'middle_name' => credential_encrypt($request->middle_name),
                    'last_name' => credential_encrypt($request->last_name),
                    'email'    => credential_encrypt($request->email),
                    'mobile'   => credential_encrypt($request->mobile),
                    'gender'   => ($request->gender),
                    'address'  => credential_encrypt($request->address),
                    'pincode'  => credential_encrypt($request->pincode),
                    'password' => Hash::make($password),
                    'totp_secret' => $totp_secret,
                    'employee_code' => $reportingEmployeeCode,
                    'status' => $request->status,
                    'usertype' => $request->user_type,
                    'zone_id' => $request->zoneId,
                    'reportingto' => $request->reportingTo,
                    'pan_no' => credential_encrypt($request->pan_no),
                    'adhar_no' => credential_encrypt($request->adhar_no),
                    'qualification' => $request->qualification,
                    'dob' => credential_encrypt($request->dob),
                    'license_start_date' => credential_encrypt($request->license_start_date),
                    'license_end_date' => credential_encrypt($request->license_end_date),
                    'pos_code' => $userCode,
                    'oemId' => $request->oemId,
                    'mispId' => $request->mispId,
                    'branchId' => $request->branchId,
                ]);

                if ($inserted) {
                    $user_id = $inserted->id;
                    $userbankdetailsreq = new UserBankDetailsReq($request->all());
                    $userbankdetails = $this->UserBankDetails($userbankdetailsreq, $user_id);

                    $request->merge(['user_id' =>  $user_id]);

                    $userrolemapping = $this->userRoleMapping->UserRoleMapping($request);

                    foreach ($request->lob_id as $value) {

                        $userlobMapping = SellNow::create([
                            'user_id' => $user_id,
                            'lob_id' => $value,
                            'created_at' => Carbon::now(),
                            'updated_at' => null,
                        ]);
                    }

                    if (!$userlobMapping) {
                        return response()->json([
                            'status' => 500,
                            'message' => 'Error While Mapping lob to User.',
                        ]);
                    }
                    if ($authenticatedUser->is_admin == 'Y' && getUserTypeIdentifier($authenticatedUser->usertype) == 'E' && $request->user_type != $reportingRoleUsertype) {
                        
                        if ($authenticatedUser->is_admin == 'Y' && getUserTypeIdentifier($authenticatedUser->usertype) == 'E' && $request->has('reportingTo')==false && in_array($request->user_type,[1,2,3])) {
                            User::where('id', $inserted->id)->update([
                                'employee_code' => $request->employeeCode,
                                'reportingto' => 0,
                                'is_admin' => "Y",
                            ]);
                        } else { 
                            $reportingEmployeeCode = User::select('employee_code')->where('id', $request->reportingTo)->first()['employee_code'] ?? 0;
                            $reportingToAdminByUsertype = User::where('is_admin', 'Y')->where('usertype', $request->user_type)->pluck('id')->first();

                            User::where('id', $inserted->id)->update([
                                'employee_code' => $reportingEmployeeCode,
                                'reportingto' => $reportingToAdminByUsertype,
                            ]);
                        }
                    }
                   
                    if (false) {
                        if ($defaultPartnerUserForPosp == 'Y' && $getusertype->Identifier == 'P') {
                            //This thing needs to be discussed
                            $partnerUsertypeId = userTypes::select('id')->where('Identifier', 'Partner')->first()['id'];
                            $this->UserMapUsertype($user_id, $partnerUsertypeId, $request->role_id, $request->reportingTo);
                        }
                    }
                    DB::commit();

                    if (config('send-password-mail') == 1) {
                        $new_email = $request->email;
                        $title = 'Login Credentials';
                        $body = 'Default Body';
    
                        // Trigger the event
                        event(new userCreation($new_email, $qrCode_generated['QrCode'], $secret, $password, $body, $title));
    
                        EmailActivityLog::create([
                            'email' => $new_email,
                            'subject' => 'User Credentials Sent',
                            'body' => $body,
                            'type' => 'User Credentials Sent',
                            'status' => 'Email Sent',
                            'sent_at' => now(),
                        ]);
                    }

                    return requestResponseMessage(['status' => 200, 'message' => 'User Created Successfully', 'data' => [
                        'email' =>  $request->email,
                        'userId' => $user_id,
                    ]]);
                } else {
                    DB::rollBack();

                    return requestResponseMessage(['status' => 404, 'message' => 'Error While Creating User.']);
                }
            } catch (\Exception $e) {
                DB::rollBack();

                return requestResponseMessage(['status' => 404, 'message' => 'Something went wrong: ' . $e->getMessage()]);
            }
        
    }

    protected function prepareUserData(array $data,$reportingEmployeeCode,$userCurrentData)
    {
        $userData= [
            'name' => credential_encrypt($data['name']),
            'middle_name' => credential_encrypt($data['middle_name'] ?? null),
            'last_name' => credential_encrypt($data['last_name'] ?? null),
            'email' => credential_encrypt($data['email'] ?? null),
            'mobile' => credential_encrypt($data['mobile']),
            'gender' => $data['gender'] ?? null,
            'address' => credential_encrypt($data['address'] ?? null),
            'pincode' => credential_encrypt($data['pincode'] ?? null),
            'password' =>  Hash::make('pass@123') ,
            // 'totp_secret' => $totp_secret,
            'employee_code' => $reportingEmployeeCode ?? null,
            'status' => $data['status'] ?? 'active',
            'usertype' => $data['user_type'] ?? null,
            'zone_id' => $data['zoneId'] ?? null,
            'reportingto' => $data['reportingTo'] ?? null,
            'pan_no' => credential_encrypt($data['pan_no'] ?? null),
            'adhar_no' => credential_encrypt($data['adhar_no'] ?? null),
            'qualification' => $data['qualification'] ?? null,
            'dob' => credential_encrypt($data['dob'] ?? null),
            'license_start_date' => credential_encrypt($data['license_start_date'] ?? null),
            'license_end_date' => credential_encrypt($data['license_end_date'] ?? null),
            'pos_code' => $data['userCode'] ?? null,
            'oemId' => $data['oemId'] ?? null,
            'mispId' => $data['mispId'] ?? null,
            'branchId' => $data['branchId'] ?? null,
        ];

        $getUser = User::find($userCurrentData->id); 
        $roles = $getUser->userRoles()
                    ->where('user_type', $getUser->usertype)
                    ->get();
         
        $userCurrentData->update($userData);
        $this->UserMapUsertype($getUser->id,$getUser->usertype,$data['role_id'],$getUser->reportingto,$getUser->employee_code);
                    return  response()->json([
                        'status' => 200,
                        'message' => 'User Mapping Created  Successfully'
                    ]);
       
    }
    public function update(Request $request)
    {
        $rules = [
            // 'username' => 'required|string',
            'name' => 'required|string',
            // 'middle_name' => 'required|string',
            // 'last_name' => 'required|string',
            'mobile' => 'required|regex:/^[0-9]{10}$/',
            'email' => 'required|email',
            // 'gender' => 'required|string|in:M,F',
            // 'address' => 'required|string',
            // 'pincode' => 'required|digits:6',
            'status' => 'required|in:N,Y',
            'user_type' => 'required|integer',
            'role_id' => 'required|integer',
            'lob_id' => 'required|array',
            // 'qualification' => 'required|integer',
            // 'dob' => 'required|date_format:d/m/Y',
            // 'adhar_no' => 'required|digits:12'
            // 'reportingRole' => 'required|integer',
            // 'reportingTo' => 'required|integer'
        ];

        $role_reporting_to = Role::where('id', $request->role_id)->pluck('reporting_role')->first();

        if ($role_reporting_to !== 0) {
            $rules['reportingRole'] = 'required|integer';
            $rules['reportingTo'] = 'required|integer'; 
        }

        $reportingEmployeeCode = null;
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (!$this->authenticatedUser->can($permission)) {
            return  requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $getusertype = userTypes::select('name', 'Identifier')->where('id', $request->user_type)->where('is_active', 'Y')->first();
        $userCode = '';

        if ($getusertype->Identifier == 'E' || $getusertype->Identifier == 'SP') {
            $validate = $request->validate([
                'employeeCode' => 'required|string',
            ]);

            $employeeExists = User::where('employee_code', $request->employeeCode)
                ->where('id', '!=', credential_decrypt($request->id))
                ->where('usertype', $request->user_type)
                ->exists();

            $mobileExists = User::where('mobile', credential_encrypt($request->mobile))
                ->where('id', '!=', credential_decrypt($request->id))
                ->exists();

            $emailExists = User::where('email', credential_encrypt($request->email))
                ->where('id', '!=', credential_decrypt($request->id))
                ->exists();

            if ($employeeExists) {
                return response()->json(['message' => 'The employee code already exists for another user.'], 400);
            }
            if ($mobileExists) {
                return response()->json(['message' => 'The mobile number already exists for another user.'], 400);
            }
            if($emailExists){
                return response()->json(['message' => 'The email already exists for another user.'], 400);
            }

            $reportingEmployeeCode = $request->employeeCode;
        }

        if ($getusertype->Identifier == 'MISP') {
            $validate = $request->validate([
                'oemId' => 'required|integer',
                'mispId' => 'required|integer',
                'branchId' => 'required|integer',
            ]);
        }
        if ($getusertype->Identifier == 'P') {
            $validate = $request->validate([
                'posCode' => 'required|string',
                'license_start_date' => 'required|date_format:d/m/Y',
                'license_end_date' => 'required|date_format:d/m/Y',
                'adhar_no' => 'required|digits:12',
                'pan_no' => 'required|regex:/^[A-Z]{5}[0-9]{4}[A-Z]$/'
            ]);
            $userCode = $request->posCode;
            $reportingEmployeeCode = $this->getPosReportingEmployeeCode($request->reportingTo);
        }
        if ($getusertype->Identifier == 'Partner') {
            $reportingEmployeeCode = $this->getPosReportingEmployeeCode($request->reportingTo);
            // $reportingEmployeeCode = $request->employeeCode ?? 0;
        }

        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()], 400);
        }

        $user = User::find(credential_decrypt($request->id));
        $qrCode_generated = generateQrcode();
        $secret = $qrCode_generated['secret'];
        $totp_secret = credential_encrypt($secret);
        //        $password = generateRandomPassword(8);

        $mapRepotingId=$request->reportingTo;
        if ($getusertype->Identifier != 'E' && $getusertype->Identifier != 'SP') {

            $getReportingUser = User::find($request->reportingTo);
            if ($getReportingUser && $request->user_type == $getReportingUser->user_type) {
                $mapRepotingId = User::where('is_admin', 'Y')
                            ->where('usertype', $request->user_type)
                            ->value('id') ?? 0;
            }
            
            if($request->employeeCode == "0" || empty($request->employeeCode)){

                $mapemployeeCode = User::select('employee_code')->where('id', $request->reportingTo)->first()['employee_code']??0;
                $request->merge([
                    'employeeCode' => $mapemployeeCode
                ]);            
            }

        }
        $userName = config('fetch_sp_details') ? credential_encrypt($request->employeeCode) : credential_encrypt($request->mobile);
        $updated = $user->update([
            'username' => $userName,
            'name'     => credential_encrypt($request->name),
            'middle_name' => credential_encrypt($request->middle_name),
            'last_name' => credential_encrypt($request->last_name),
            'email'    => credential_encrypt($request->email),
            'mobile'   => credential_encrypt($request->mobile),
            'gender'   => $request->gender,
            'address'  => credential_encrypt($request->address),
            'pincode'  => credential_encrypt($request->pincode),
            //            'password' => Hash::make($password),
            'totp_secret' => $totp_secret,
            'status' => $request->status,
            'usertype' => $request->user_type,
            'zone_id' => $request->zoneId,
            'reportingto' => $mapRepotingId,
            'employee_code' => $reportingEmployeeCode ?? '',
            'pan_no' => credential_encrypt($request->pan_no),
            'adhar_no' => credential_encrypt($request->adhar_no),
            'qualification' => $request->qualification,
            'dob' => credential_encrypt($request->dob),
            'pos_code' => $userCode,
            'oemId' => $request->oemId,
            'mispId' => $request->mispId,
            'branchId' => $request->branchId,
        ]);

        $userbankdetailsreq = new UserBankDetailsReq($request->all());
        $userbankdetails = $this->UserBankDetails($userbankdetailsreq, credential_decrypt($request->id));

        DB::table('model_has_roles')
            ->where('model_id', credential_decrypt($request->id))
            ->update([
                'role_id' => $request->role_id
            ]);

        $userlobmappings = SellNow::where('user_id', credential_decrypt($request->id))->delete();

        foreach ($request->lob_id as $value) {

            $userlobMapping = SellNow::create([
                'user_id' => credential_decrypt($request->id),
                'lob_id' => $value,
                'created_at' => Carbon::now(),
                'updated_at' => Carbon::now(),
            ]);
        }

        if (!$userlobMapping) {
            return response()->json([
                'status' => 500,
                'message' => 'Error While Mapping lob to User.',
            ]);
        }

        if ($updated) {
            return  requestResponseMessage(['status' => 200, 'message' => 'User Updated Successfully', 'data' => ['email' => $request->email]]);
        } else {
            return  requestResponseMessage(['status' => 404, 'message' => 'Error While Updating User.']);
        }
    }

       public function userListingOld(Request $request)
    {
        set_time_limit(0);
        ini_set('memory_limit','-1');

            $user = Auth::user();
            if ($inactiveResponse = checkUserActivity($request)) {
                return $inactiveResponse;
            }
    
            $userListingPermission = 'User Creation.view';
            if (!$user->can($userListingPermission)) {
                return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
            }
    
            $rolecondition = false;
            $finalMappingData = [];
            $finalMappingData = $this->userService->listRoleService();
            if(empty($finalMappingData)){
                $rolecondition = true;
                $userHierarchyData = $user->is_admin === 'Y'
                ? User::select('id', 'reportingto', 'employee_code')
                    ->where('usertype', $user->userType->id)
                    ->get()
                : getUserLowerHierarchy($user->id, $user->userType->id);
            $userHierarchyData = collect($userHierarchyData);
            $userHierarchyIds = $userHierarchyData->pluck('id')->toArray();
            $userHierarchyEmpCodes = $userHierarchyData->pluck('employee_code')->toArray();
            $userHierarchyEmpCodes[] = $user->employee_code;
    
            $userTypeIdentifier = userTypes::where('id', $user->usertype)->value('Identifier');
    
            if ($userTypeIdentifier === 'E' && $user->is_admin === 'N') {
                $finalMappingData = getMapPosPartner($userHierarchyEmpCodes);
                $finalMappingData = array_filter($finalMappingData, fn($item) => $item['id'] !== $user->id);
            }
            }
    
            $usersQuery = User::select([
                    'users.id', 'users.name', 'users.middle_name', 'users.last_name',
                    'users.dob', 'users.license_start_date', 'users.license_end_date',
                    'users.email', 'users.address', 'users.pincode', 'users.gender',
                    'users.usertype', 'users.mobile', 'users.username', 'users.reportingto',
                    'users.bank_branch', 'users.bank_name', 'users.bank_city', 'users.account_no',
                    'users.ifsc_code', 'users.account_holder_name', 'users.employee_code',
                    'users.pos_code', 'users.adhar_no', 'users.pan_no', 'users.oemId',
                    'users.mispId', 'users.branchId', 'users.zone_id', 'users.status',
                    'users.qualification', 'users.profile_image', 'users.user_code'
                ])
                ->leftJoin('users as parent', 'users.reportingto', '=', 'parent.id')
                ->where('users.username', '!=', credential_encrypt('super_admin'))
                ->where('users.usertype', '!=', 5)
                ->orderBy('users.id', 'desc');
    
            if ($request->filled('id')) {
                $usersQuery->where('users.id', credential_decrypt($request->id));
            }
    
            if ($request->filled('roleName')) {
                $usersQuery->join('model_has_roles', 'users.id', '=', 'model_has_roles.model_id')
                    ->join('roles', 'roles.id', '=', 'model_has_roles.role_id')
                    ->where('roles.name', $request->roleName);
            }
    
            if ($request->filled('usertype')) {
                $usersQuery->where('users.usertype', $request->usertype);
            }
    
            if ($request->filled('search')) {
                $search = credential_encrypt($request->search);
                $usersQuery->where(function ($query) use ($search) {
                    $query->where('users.name', 'like', "%{$search}%")
                        ->orWhere('users.email', 'like', "%{$search}%")
                        ->orWhere('users.mobile', 'like', "%{$search}%")
                        ->orWhere('users.username', 'like', "%{$search}%")
                        ->orWhere('users.middle_name', 'like', "%{$search}%")
                        ->orWhere('users.last_name', 'like', "%{$search}%")
                        ->orWhere('users.user_code', 'like', "%{$search}%")
                        ->orWhere('users.employee_code', 'like', "%{$search}%");
                });
            }
            if($rolecondition){
            $userTypeId = userTypes::where('Identifier', 'E')->value('id');
            if ($user->usertype == $userTypeId) {
                $finalMappingIds = array_column($finalMappingData, 'id');
                $idsToFilter = array_unique(array_merge($finalMappingIds, $userHierarchyIds));
                if ($user->is_admin !== 'Y') {
                    $usersQuery->whereIn('users.id', $idsToFilter);
                }
            } else {
                $usersQuery->whereIn('users.id', $userHierarchyIds);
            }
            }else{
                $usersQuery->whereIn('users.id', $finalMappingData);
            }
            if ($request->filled('user_status')) {
                $usersQuery->where('users.status', $request->user_status);
            }
    
            $perPage = $request->input('show', 10);
            $users = $request->input('paginate')
                ? $usersQuery->paginate($perPage)
                : $usersQuery->get();
                
            // dd($users->total());
            $zoneData = ZoneMasterModel::select('id', 'office_zone')->get()->keyBy('id');
            $reportingUsers = User::select('id', 'name')->get()->keyBy('id');
            $reportingRoles = DB::table('model_has_roles')
                ->join('roles', 'roles.id', '=', 'model_has_roles.role_id')
                ->where('model_has_roles.model_type', 'App\\Models\\User')
                ->select('roles.name', 'roles.id', 'model_has_roles.model_id')
                ->get()
                ->keyBy('model_id');
    
                 
                if ($request->filled('id')) {
                $userLobs = SellNow::select('user_lob_relation.lob_id as id', 'lob_master.lob as name', 'user_lob_relation.user_id')
                    ->join('lob_master', 'lob_master.id', '=', 'user_lob_relation.lob_id')
                    ->whereNull('user_lob_relation.deleted_at')
                    ->get()
                    ->groupBy('user_id');
                $qualifications = QualificationMaster::select('qualification_master_id as id', 'qualification_name as name')->get()->keyBy('id');
                }
    
                
                $userTypes = userTypes::select('id', 'name', 'Identifier')->get()->keyBy('id');
                $rolesDetails = Role::select('id', 'name')->get()->keyBy('name');
                
                $usersData = [];
                $index = ($users instanceof \Illuminate\Pagination\LengthAwarePaginator || $users instanceof \Illuminate\Pagination\Paginator)
                    ? ($users->currentPage() - 1) * $users->perPage()
                    : 0;
                    $UpdatedPospRoleConfig = config('Updated.Posp.Role');
                 $reportingUsersEmployee = User::select('id', 'name', 'employee_code')
                    ->where('usertype', '1')
                    ->get()
                    ->keyBy('employee_code');
                foreach ($users as $userItem) {
                    $userRoles = $userItem->getRoleNames()->toArray();
                    $primaryRole = $userRoles[0] ?? null;
    
                    $assignSupervisor = ($UpdatedPospRoleConfig == 'Y' && $userItem->usertype == 2 );
                    $roleDetail = $rolesDetails[$primaryRole] ?? null;
                
                    $reportingTo = $reportingUsers[$userItem->reportingto] ?? null;
                    $reportingRole = $reportingRoles[$userItem->reportingto] ?? null;
                
                    $reportingToEmployee = $reportingUsersEmployee[$userItem->employee_code] ?? null;
                    $reportingToRoleEmployee = $reportingToEmployee ? $reportingRoles[$reportingToEmployee->id] ?? null : null;
                
                    $usertypeDetail = $userTypes[$userItem->usertype] ?? null;
                    $zone = $zoneData[$userItem->zone_id] ?? null;
                
                    $userData = [
                        'sr_no' => ++$index,
                        'id' => credential_encrypt($userItem->id),
                        'name' => credential_decrypt($userItem->name),
                        'middle_name' => credential_decrypt($userItem->middle_name),
                        'last_name' => credential_decrypt($userItem->last_name),
                        'email' => credential_decrypt($userItem->email),
                        'address' => credential_decrypt($userItem->address),
                        'pincode' => credential_decrypt($userItem->pincode),
                        'mobile' => credential_decrypt($userItem->mobile),
                        'username' => credential_decrypt($userItem->username),
                        'parent_username' => credential_decrypt($userItem->parent_username),
                        'gender' => $userItem->gender,
                        'bank_branch' => credential_decrypt($userItem->bank_branch),
                        'bank_name' => credential_decrypt($userItem->bank_name),
                        'bank_city' => credential_decrypt($userItem->bank_city),
                        'account_no' => credential_decrypt($userItem->account_no),
                        'ifsc_code' => credential_decrypt($userItem->ifsc_code),
                        'account_holder_name' => credential_decrypt($userItem->account_holder_name),
                        'employeeCode' => ($userItem->usertype==1 || $userItem->usertype==7) ? $userItem->employee_code : $userItem->user_code,
                        'dob' => credential_decrypt($userItem->dob),
                        'license_start_date' => credential_decrypt($userItem->license_start_date),
                        'license_end_date' => credential_decrypt($userItem->license_end_date),
                        'posCode' => $userItem->pos_code,
                        'adhar_no' => credential_decrypt($userItem->adhar_no),
                        'pan_no' => credential_decrypt($userItem->pan_no),
                        'Status' => $userItem->status == 'Y' ? 'Active' : 'Inactive',
                        'zoneId' => [
                            'id' => $userItem->zone_id,
                            'office_zone' => $zone->office_zone ?? null,
                        ],
                        'parent_name' => $reportingTo ? credential_decrypt($reportingTo->name): null,
                        'reportingRole' => $reportingRole,
                        'reportingTo' => $reportingTo ? [
                            'id' => $reportingTo->id,
                            'name' => credential_decrypt($reportingTo->name),
                        ] : null,
                        'reporting_Employee_Role' => ($userItem->usertype == 1 || $userItem->usertype == 7)
                            ? $reportingRole
                            : ($reportingToRoleEmployee ? $reportingToRoleEmployee: null),
                        'reporting_Employee' => ($userItem->usertype == 1 || $userItem->usertype == 7)
                            ? ($reportingTo ? [
                                'id' => $reportingTo->id,
                                'name' => credential_decrypt($reportingTo->name),
                            ] : null)
                            : ($reportingToEmployee ?  ['id' => $reportingToEmployee->id,'name' => credential_decrypt($reportingToEmployee->name)]: null),
                        'usertype' => $usertypeDetail ? [
                            'id' => $usertypeDetail->id,
                            'name' => $usertypeDetail->name,
                            'Identifier' => $usertypeDetail->Identifier,
                        ] : null,
                        'role' => $roleDetail ? [
                            'id' => $roleDetail->id,
                            'name' => $roleDetail->name,
                        ] : null,
                        'assignSupervisor' => $assignSupervisor,
                    ];
                
                    // Add lob if available
                    if ($request->filled('id') && isset($userLobs[$userItem->id])) {
                        $userData['lob_id'] = $userLobs[$userItem->id];
                    }
                
                    // Add qualification if available
                    if ($request->filled('id') && isset($qualifications[$userItem->qualification])) {
                        $userData['qualification'] = $qualifications[$userItem->qualification];
                    }
                
                    $usersData[] = $userData;
    
                }            
    
            return response()->json([
                'status' => true,
                'data' => $usersData,
                'message' => 'User listing fetched successfully.',
                'LastPage' => $request->input('paginate')?$users->lastPage():'',
                'total' => $request->input('paginate')?$users->total():''      
            ]);
        }

    private function UserMapUsertype($userId,$usertype,$role_id,$reportingTo,$employee_code='')
    {
        //  $user = Auth::user();
        //  $userListingPermission = 'User Creation.view';
        // if (!$user->can($userListingPermission)) {
        //     return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        // }
        $checkInMappings = UserMapping::where('user_id', $userId)->where('user_type', $usertype)->first();
        if($checkInMappings)
        {
            return requestResponseMessage(['status' => 500, 'message' => 'User  Already Exists please Try with other email username and mobile number']);
        }
        $PresentUserId = $userId;
        UserMapping::insert([
            'user_id' => $PresentUserId,
            'user_type' => $usertype,
            'role_id' => $role_id,
            'reportingto' => $reportingTo,
            'employee_code' => $employee_code,
            'created_at' => Carbon::now(),
        ]);
    
        // try {
            DB::table('model_has_roles')->insert([
                'role_id' => $role_id,
                'model_type' => 'App\Models\User',
                'model_id' => $userId,
            ]);
        // } catch (\Illuminate\Database\QueryException $e) {
        //     // Error code for duplicate entry (MySQL)
        //     if ($e->errorInfo[1] == 1062) {
        //         // Duplicate entry - handle gracefully
        //         // Log::info("Role already assigned to user: $userId");
        //     } else {
        //         throw $e; // Re-throw other database errors
        //     }
        // }

    }
    
    public function CustomerList(Request $request)
    {
         $user = Auth::user();
        $userListingPermission = 'User Creation.view';
        if (!$user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $size = $request->input('size', 10);
        $pageNo = $request->input('page', 1);
        $data = User::select('id', 'name', 'middle_name', 'last_name', 'email', 'usertype', 'mobile', 'username')
            ->where('usertype', getUserTypeIdByIdentifier('U'))
            ->paginate($size);

        $customerData = $data->map(function ($customer,$index) use ($request,$size,$pageNo) {
        
            $decrypted = [
                'sr_no' => $pageNo * $size - $size + ($index + 1),
                'name' => credential_decrypt($customer->name),
                'email' => credential_decrypt($customer->email),
                'mobile' => credential_decrypt($customer->mobile),
                'username' => credential_decrypt($customer->username)
            ];

            foreach (['name', 'email', 'mobile', 'username'] as $field) {
                if ($request->filled($field) && stripos($decrypted[$field], $request->$field) === false) {
                    return null;
                }
            }
  
            return [
                'sr_no' => $decrypted['sr_no'],
                'id' => $customer->id,
                'name' => $decrypted['name'],
                'middle_name' => credential_decrypt($customer->middle_name),
                'last_name' => credential_decrypt($customer->last_name),
                'email' => $decrypted['email'],
                'mobile' => $decrypted['mobile'],
                // 'username' => $decrypted['username'],
            ];
        })->filter()->values();

        if ($request->has('search_value') && !empty($request->search_value)) {
            $customerData = $customerData->filter(function ($item) use ($request) {
                return stripos($item['name'], $request->search_value) !== false || 
                stripos($item['email'], $request->search_value) !== false || 
                stripos($item['mobile'], $request->search_value) !== false;
            })->values();
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                ["header" => "Sr No", "accessorKey" => "sr_no", "isActions" => 'integer'],
                // ["header" => "ID", "accessorKey" => "id", "isActions" => 'integer'],
                ["header" => "Name", "accessorKey" => "name", "isActions" => 'string'],
                ["header" => "Middle Name", "accessorKey" => "middle_name", "isActions" => 'string'],
                ["header" => "Last Name", "accessorKey" => "last_name", "isActions" => 'string'],
                ["header" => "Email", "accessorKey" => "email", "isActions" => 'string'],
                ["header" => "Mobile", "accessorKey" => "mobile", "isActions" => 'string'],
                // ["header" => "Username", "accessorKey" => "username", "isActions" => 'string'],
            ],
            'return_data' => $customerData,
            'pagination' => [
                'total_records' => $data->total(),
                'total_pages' => $data->lastPage(),
                'current_page' => $data->currentPage(),
                'per_page' => $data->perPage(),
            ],
        ]);
    }
    public function manageUserAccess(Request $request)
    {
        $user = Auth::user();
         $userListingPermission = 'User Creation.view';
        if (!$user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $validatedData = $request->validate([
            'user_id' => 'required',//exists:users,id
            'b2c' => 'boolean',
            'userCreation' => 'boolean',
            'employee' => 'boolean',
            'pos' => 'boolean',
            'partner' => 'boolean',
            'employee_list' =>'boolean',
            'pos_list'=>'boolean',
            'partner_list'=>'boolean'
        ]);

        $user = User::find(credential_decrypt($validatedData['user_id']));

        if (!$user) {
            return response()->json(['error' => 'User not found'], 404);
        }

        $is_b2c_flag = $validatedData['b2c'] ?? false;
        // $user_creation_flag = $validatedData['userCreation'] ?? false;

        $dataFlag = [];
        if ($validatedData['employee'] ?? false) {
            $dataFlag[] = 'E';
        }
        if ($validatedData['pos'] ?? false) {
            $dataFlag[] = 'P';
        }
        if ($validatedData['partner'] ?? false) {
            $dataFlag[] = 'Partner';
        }
        $listFlag = [];
        if ($validatedData['employee_list'] ?? false) {
            $listFlag[] = 'E';
        }
        if ($validatedData['pos_list'] ?? false) {
            $listFlag[] = 'P';
        }
        if ($validatedData['partner_list'] ?? false) {
            $listFlag[] = 'Partner';
        }

        $user->update([
            'is_b2cflag' => $is_b2c_flag,
            // 'userCreation' => $user_creation_flag,
            'list_flag' => implode(',',$listFlag),
            'data_flag' => implode(',', $dataFlag), 
        ]);

        return response()->json(['status' => 200,'message' => 'User access updated successfully'], 200);

    }
    public function prefillManageAccessData(Request $request)
    {
        $user = Auth::user();
         $userListingPermission = 'User Creation.view';
        if (!$user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $user = User::find(credential_decrypt($request['user_id']));

        if (!$user) {
            return response()->json(['status' => 404, 'message' => 'User not found'], 404);
        }

        $dataFlagArray = explode(',', $user->data_flag ?? '');
        $listFlagArray = explode(',',$user->list_flag ?? '');

        $responseData = [
            'b2c' => (bool) $user->is_b2cflag,
            'userCreation' => false,
            'employee' => in_array('E', $dataFlagArray),
            'pos' => in_array('P', $dataFlagArray),
            'partner' => in_array('Partner', $dataFlagArray),
            'employee_list' => in_array('E', $listFlagArray),
            'pos_list' => in_array('P', $listFlagArray),
            'partner_list' => in_array('Partner', $listFlagArray),
        ];

        return response()->json([
            'status' => 200,
            'return_data' => $responseData
        ], 200);
    }


    public function getDirectUserMapping(Request $request)
    {
        $userListingPermission = 'User Creation.view';
        if (!$this->authenticatedUser->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $validator = Validator::make($request->all(), [
            'user_id' => 'required|not_in:1',
        ]);
    
        if ($validator->fails()) {
            return response()->json([
                'status' => 422,
                'errors' => $validator->errors(),
            ]);
        }

        $userEmployeeCode = User::where('id', credential_decrypt($request->user_id))->pluck('employee_code')->first();
        if (!$userEmployeeCode) {
            return response()->json([
                'status' => 404,
                'message' => 'User not found',
            ]);
        }

        // $users = User::select('id', 'name', 'mobile', 'profile_image', 'reportingto', 'employee_code')->with('roles')->where('reportingto', credential_decrypt($request->user_id))->orWhere('employee_code', $userEmployeeCode)->get();
        $users = User::select('id', 'name', 'mobile', 'profile_image', 'reportingto', 'employee_code')
                ->with('roles')
                ->where(function ($q) use ($request, $userEmployeeCode) {
                    $q->where('reportingto', credential_decrypt($request->user_id))
                    ->orWhere('employee_code', $userEmployeeCode);
                })
                ->where('id', '!=', credential_decrypt($request->user_id))
                ->get();
        

        $currentRequestedUser = User::select('id', 'name', 'mobile', 'profile_image', 'reportingto', 'employee_code')->with('roles')->where('id', credential_decrypt($request->user_id))->first();

        $google_image = Storage::disk('public')->url('profile_images/fallback_user_img.png');

        $formatted = $users->map(function ($user) use ($google_image, $currentRequestedUser) {
            return [
                'id' => credential_encrypt($user->id),   // unique identifier
                'data' => [
                    'user_id' => credential_encrypt($user->id),
                    'label' => credential_decrypt($user->name),
                    'mobile' => credential_decrypt($user->mobile),
                    'direct_reporting_users_count' => User::where('reportingto', $user->id)->count(),
                    'role_id' => optional($user->roles->first())->id,  // if roles is not assigned then it will return null because of optional
                    'role' => optional($user->roles->first())->name,
                    'reportingto' => $user->reportingto,
                    'image' => $user->profile_image ?? $google_image,
                ],
                'parentId' => credential_encrypt($currentRequestedUser->id),    // Jo parent ka Unique identifier hai
                'type' => 'customNode',


            ];
        });

        $data = [];
        $data[] = [
            'id' => credential_encrypt($currentRequestedUser->id),   // unique identifier (parent ka unique identifier child ka parentId hoga)
            'data' => [
                'user_id' => credential_encrypt($currentRequestedUser->id),
                'label' => credential_decrypt($currentRequestedUser->name),
                'mobile' => credential_decrypt($currentRequestedUser->mobile),
                'image' => $currentRequestedUser->profile_image ?? $google_image,
                'reportingto' => $currentRequestedUser->reportingto,
                'previousParentId' => credential_encrypt($currentRequestedUser->reportingto),
                'direct_reporting_users_count' => User::where('reportingto', $currentRequestedUser->id)->count(),
                'role' => optional($currentRequestedUser->roles->first())->name,
                'role_id' => optional($currentRequestedUser->roles->first())->id,
            ],
            'type' => 'customNode',
            'children' => $formatted,

        ];

        return response()->json([
            'status' => 200,
            'data' => $data,
        ]);
    }

    public function getDirectUserMappingTable(Request $request)
    {
        $userListingPermission = 'User Creation.view';
        if (!$this->authenticatedUser->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $column_head = [
            [
                "header" => "Sr No",
                "accessorKey" => "sr_no",
                "type" => "string"
            ],
            [
                "header" => "Name",
                "accessorKey" => "label",
                "type" => "string"
            ],
            [
                "header" => "Mobile",
                "accessorKey" => "mobile",
                "type" => "string"
            ],
            [
                "header" => "Direct_Reporting_Users_Count",
                "accessorKey" => "direct_reporting_users_count",
                "type" => "reporting_button"
            ],
            [
                "header" => "Role",
                "accessorKey" => "role",
                "type" => "string"
            ],
            // [
            //     "header" => "ReportingTo",
            //     "accessorKey" => "reportingto",
            //     "type" => "string"
            // ],
        ];


        $validator = Validator::make($request->all(), [
            'user_id' => 'required|not_in:1',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 422,
                'errors' => $validator->errors(),
            ]);
        }

        $userEmployeeCode = User::where('id', credential_decrypt($request->user_id))->pluck('employee_code')->first();
        if (!$userEmployeeCode) {
                return response()->json([
                'status' => 404,
                'message' => 'User not found',
            ]);
        }

        $google_image = Storage::disk('public')->url('profile_images/fallback_user_img.png');

        $output = [];
        $index = 0;

        if ($request->has('firstRedirect') && $request->firstRedirect === true) {

            $currentRequestedUser = User::select('id', 'name', 'mobile', 'profile_image', 'reportingto', 'employee_code', 'usertype')->with('roles')->where('id', credential_decrypt($request->user_id))->first();
            if($currentRequestedUser->usertype == 1){
                $mappedUserCount = User::where(function ($q) use ($currentRequestedUser) {
                    $q->where('reportingto', credential_decrypt($currentRequestedUser->id))
                        ->orWhere(function ($ql) use ($currentRequestedUser) {
                            $ql->where('usertype', '!=',1)
                            ->Where('employee_code', $currentRequestedUser->employee_code);
                        });
                    })
                    ->where('id', '!=', credential_decrypt($currentRequestedUser->id))
                    ->count();
            }else{
                $mappedUserCount = User::where('reportingto', credential_decrypt($currentRequestedUser->id))
                    ->count();
            }

            $output[] = [
                    'sr_no' => ++$index,
                    'user_id' => credential_encrypt($currentRequestedUser->id),
                    'label' => credential_decrypt($currentRequestedUser->name),
                    'mobile' => credential_decrypt($currentRequestedUser->mobile),
                    'image' => $currentRequestedUser->profile_image ?? $google_image,
                    'reportingto' => $currentRequestedUser->reportingto,
                    'direct_reporting_users_count' => $mappedUserCount,
                    // 'direct_reporting_users_id' => User::where('reportingto', $currentRequestedUser->id)->pluck('id')->toArray(),
                    'role' => optional($currentRequestedUser->roles->first())->name,
                    'role_id' => optional($currentRequestedUser->roles->first())->id,
                ];
            
            return response()->json([
                'status' => 200,
                'return_data' => $output,
                'column_head' => $column_head,
            ]);
        }

        if ($request->has('getReportingUsers') && $request->getReportingUsers === true) {

            $reportingUsers = User::select('id', 'name', 'mobile', 'profile_image', 'reportingto', 'employee_code')
                ->with('roles')
                ->where(function ($q) use ($request, $userEmployeeCode) {
                    $q->where('reportingto', credential_decrypt($request->user_id))
                    ->orWhere(function ($ql) use ($userEmployeeCode) {
                        $ql->where('usertype', '!=',1)
                        ->Where('employee_code', $userEmployeeCode);
                    });
                })
                ->where('id', '!=', credential_decrypt($request->user_id))
                ->get();

            foreach ($reportingUsers as $reportingUser) {
                $output[] = [
                    'sr_no' => ++$index,
                    'user_id' => credential_encrypt($reportingUser->id),
                    'label' => credential_decrypt($reportingUser->name),
                    'mobile' => credential_decrypt($reportingUser->mobile),
                    'image' => $reportingUser->profile_image ?? $google_image,
                    'reportingto' => $reportingUser->reportingto,
                    'direct_reporting_users_count' => User::where('reportingto', $reportingUser->id)->count(),
                    // 'direct_reporting_users_id' => User::where('reportingto', $currentRequestedUser->id)->pluck('id')->toArray(),
                    'role' => optional($reportingUser->roles->first())->name,
                    'role_id' => optional($reportingUser->roles->first())->id,
                ];
            }

            return response()->json([
                'status' => 200,
                'return_data' => $output,
                'column_head' => $column_head,
            ]);
        }

        


    }

    public function makeSupervisor(Request $request){

        $userListingPermission = 'User Creation.view';
        if (!$this->authenticatedUser->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        
        $validator = Validator::make($request->all(), [
            'user_id' => 'required',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 422,
                'errors' => $validator->errors(),
            ]);
        }

        $user = User::find(credential_decrypt($request->user_id));
        if (!$user) {
            return response()->json(['status' => 404, 'message' => 'User not found'], 404);
        }
        $supervisorRoleId = Role::where('name', 'Supervisor')->pluck('id')->first();
        if (!$supervisorRoleId) {
            return response()->json(['status' => 404, 'message' => 'Supervisor role not found'], 404);
        }

        if($user->usertype == 2){
            
          $updated=DB::table('model_has_roles')
            ->where('model_id', credential_decrypt($request->user_id))
            ->update([
                'role_id' => $supervisorRoleId
            ]);
        }else{
            return response()->json(['status' => 500, 'message' => 'Only Posp Can be assigned to Supervisor Role'], 200);
        }

        return response()->json(['status' => 200, 'message' => 'Role updated successfully'], 200);
    }

    public function passwordUpdate(Request $request)
    {
        $userListingPermission = 'User Creation.view';
        if (!$this->authenticatedUser->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $rules = [
            'old_password' => 'required|string',
            'password' => [
                'required',
                'string',
                'min:8',
                'regex:/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/'
            ],
            'confirm_password' => 'required|string|same:password',
        ];

        $messages = [
            'old_password.required' => 'The old password field is required.',
            'password.required' => 'The password field is required.',
            'password.min' => 'The password must be at least 8 characters.',
            'password.regex' => 'The password must contain at least one uppercase letter, one lowercase letter, one number, and one special character.',
            'confirm_password.required' => 'The confirm password field is required.',
            'confirm_password.same' => 'The confirm password and password must match.',
        ];

        $validator = Validator::make($request->all(), $rules, $messages);

        if ($validator->fails()) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Validation fails',
                'errors' => $validator->errors()
            ], 500);
        }

        $user = Auth::user();

        if (!Hash::check($request->old_password, $user->password)) {
            return response()->json([
                'status' => false,
                'message' => 'Old password does not match.'
            ], 401);
        }

        if($request->old_password === $request->password){
            return response()->json([
                'status' => false,
                'message' => 'old password and new password cannot be same change your new password.'
            ], 401);
        }

        $check=User::where('id', $user->id)->update([
            'password' => Hash::make($request->password)
        ]);

        if($check){
            return response()->json([
                'status' => true,
                'message' => 'Password updated successfully.'
            ],200);
        }else{
            return response()->json([
                'status' => false,
                'message' => 'Password updated failed.'
            ],500);
        }

        
    }
    public function checkMobile(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'mobile' => 'required|digits_between:10,15',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'message' => 'Validation Error.',
                'errors' => $validator->errors()
            ], 422);
        }

         $mobile = $request->input('mobile');

        $userExists = User::where('mobile', credential_encrypt($mobile))->exists();

        if($userExists){
            return response()->json([
                'status' => true,
                'mobile' => $mobile,
                'exists' => $userExists,
                'message' => $userExists ? 'Mobile number already exists.' : 'Mobile number is available.',
            ],200);
        }else{
            return response()->json([
                'status' => false,
                'mobile' => $mobile,
                'exists' => $userExists,
                'message' => $userExists ? 'Mobile number already exists.' : 'Mobile number is available.',
           ],200);
        }
 
    }

    public function checkEmail(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'email' => 'required|email|max:255',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'message' => 'Validation Error.',
                'errors' => $validator->errors()
            ], 422);
        }

        $email = $request->input('email');

        $userExists = User::where('email', credential_encrypt($email))->exists();

        if($userExists){
            return response()->json([
                'status' => true,
                'email' => $email,
                'exists' => $userExists,
                'message' => $userExists ? 'Email already exists.' : 'Email is available.',
            ],200);
        }else{
            return response()->json([
                'status' => false,
                'email' => $email,
                'exists' => $userExists,
                'message' => $userExists ? 'Email already exists.' : 'Email is available.',
           ],200);
        }
 
    }
        
    public function ssoDashboardListing(Request $request)
    {
        $ssoData = SSO::select('id', 'sso_api_token', 'status', 'created_at')->get();
        return response()->json([
            'status' => 200,
            'data' => $ssoData,
            'message' => 'SSO token listing fetched successfully.',
        ]);
    }  
    
    public function ssoMotorTokenListing(Request $request)
    {
        $journeyData = TokenModel::select(
                'journey_api_token.xutm',
                'journey_api_token.seller_id',
                'journey_api_token.lob_id',
                'journey_api_token.created_at',
                'users.name as seller_name',
            )
            ->leftJoin('users', 'users.id', '=', 'journey_api_token.seller_id')
            ->get();

        return response()->json([
            'status' => 200,
            'data' => $journeyData,
            'message' => 'SSO motor token listing fetched successfully.',
        ]);
    }
    
    public function searchEmployee(Request $request)
    {
        $user = Auth::user();
        $term = $request->input('term');
        $userType = $user->usertype;
        $userId = $user->id;
        $dataFetchFrom = config('data_fetch_from_old') ? 'old_user_id' : 'id';
        $UserIdentifier = getUserTypeFromToken();
        $hierarchyData = getUserLowerHierarchy($userId, $userType);
        if (empty($hierarchyData)) {
                $usersIdWithTypetoFetch[$UserIdentifier] = [$user->{$dataFetchFrom}];
                $getUserEmpCode = $user->employee_code;

                if($userType == 1){
                    $sp_exists = userTypes::where('Identifier', 'SP')->exists();
                    if($sp_exists){
                        $usersIdWithTypetoFetch['SP'] = [$user->{$dataFetchFrom}];
                    }
                    $finalMappingData = getMapPosPartner([$getUserEmpCode]);
                                            $finalpospartnerdata = collect($finalMappingData)
                                                ->groupBy('usertype')
                                                ->mapWithKeys(function ($group, $key) use ($dataFetchFrom) {
                                                    return [
                                                        $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck($dataFetchFrom)->all()
                                                    ];
                                                })
                                                ->toArray();
                    if(!empty($finalpospartnerdata)){
                        $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                    }
                } 
            }else {
                $usersIdWithTypetoFetch = [
                        $UserIdentifier => array_column($hierarchyData, $dataFetchFrom)
                    ];
                    $allemployeedata = array_column($hierarchyData, 'employee_code');
                    $allemployeedata[] = $user->employee_code;
                    $usersIdWithTypetoFetch[$UserIdentifier] = array_merge($usersIdWithTypetoFetch[ $UserIdentifier], [$userId]);

                    
                if($userType == 1){
                    $sp_exists = userTypes::where('Identifier', 'SP')->exists();
                    if($sp_exists){
                        $usersIdWithTypetoFetch['SP'] = [$user->{$dataFetchFrom}];
                    }
                    $finalMappingData = getMapPosPartner($allemployeedata);
                                            $finalpospartnerdata = collect($finalMappingData)
                                                ->groupBy('usertype')
                                                ->mapWithKeys(function ($group, $key) use ($dataFetchFrom) {
                                                    return [
                                                        $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck($dataFetchFrom)->all()
                                                    ];
                                                })
                                                ->toArray();
                    if(!empty($finalpospartnerdata)){
                        $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                    }
                }   

            }

        $mappedUserIds = collect($usersIdWithTypetoFetch)
                        ->flatten()
                        ->unique()
                        ->values()
                        ->toArray();

        $usernames = DB::table('users')
                    ->whereIn($dataFetchFrom, $mappedUserIds)
                    ->pluck('username')
                    ->map(fn ($u) => credential_decrypt($u))
                    ->toArray();

        $employees = DB::table('employee_payroll_id')
        ->whereIn('ANA_RM_ID', $usernames)
        ->where(function ($query) use ($term) {
            $query->where('employee_name', 'like', $term . '%')
                  ->orWhere('user_name', 'like', $term . '%');
        })
        ->limit(100)
        ->get();

        $formatted = $employees->map(function ($emp) {
            return [
                "employee_name" => "{$emp->employee_name} ({$emp->user_name})",
                "user_name"     => $emp->user_name,
            ];
        });

        if ($employees->isEmpty()) {
            return response()->json([
                'status' => false,
                'message' => 'No employees found for the given search term.',
                'data' => []
            ], 404);
        }

        return response()->json([
            'status' => true,
            'message' => 'Employees fetched successfully.',
            'data' => $formatted
        ]);
    }

    public function searchEmployeeByBranchCode(Request $request)
    { 
        $request->validate([
            'category' => 'required|string',
        ]);
    
        $branchCode = $request->input('category');
    
        $employees = DB::table('employee_payroll_id')
            ->select('employee_name', 'user_name')
            ->where('rm_branch_code', $branchCode)
            ->get();
    
        if ($employees->isEmpty()) {
            return response()->json([
                'status'  => false,
                'message' => 'No employees found for the given branch code.',
                'data'    => []
            ], 200);
        }
    
        $formatted = $employees->map(function ($emp) {
            return [
                'employee_name' => "{$emp->employee_name} ({$emp->user_name})",
                'user_name'     => $emp->user_name,
            ];
        });
    
        return response()->json([
            'status'  => true,
            'message' => 'Employees fetched successfully.',
            'data'    => $formatted
        ], 200);
    }

    public function businessType()
    {
        
        $raw = config('businessType');
    
        $codes = json_decode($raw, true);
    
        $formatted = array_map(function ($item) {
            return [
                'label' => $item,
                'value' => $item,
            ];
        }, $codes);
    
        return response()->json([
            'status' => 200,
            'data' => $formatted,
            'message' => 'Code types fetched successfully.',
        ]);
    }

    public function userListing(Request $request)
    {
        set_time_limit(0);
        ini_set('memory_limit','-1');
        $user = Auth::user();

        if ($inactiveResponse = checkUserActivity($request)) {
            return $inactiveResponse;
        }

        if (!$user->can('User Creation.view')) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $UpdatedPospRoleConfig = config('Updated.Posp.Role');

        /* ==============================
            PRELOAD REQUIRED DATA
        ===============================*/

        $rolecondition = false;
        $finalMappingData = [];
        $finalMappingData = $this->userService->listRoleService();
        if(empty($finalMappingData)){
            $rolecondition = true;
            $userHierarchyData = $user->is_admin === 'Y'
            ? User::select('id', 'reportingto', 'employee_code')
                ->where('usertype', $user->userType->id)
                ->get()
            : getUserLowerHierarchy($user->id, $user->userType->id);
            
            $userHierarchyData = collect($userHierarchyData);
            $userHierarchyIds = $userHierarchyData->pluck('id')->toArray();
            $userHierarchyEmpCodes = $userHierarchyData->pluck('employee_code')->toArray();
            $userHierarchyEmpCodes[] = $user->employee_code;

            $userTypeIdentifier = userTypes::where('id', $user->usertype)->value('Identifier');
    
            if ($userTypeIdentifier === 'E' && $user->is_admin === 'N') {
                $finalMappingData = getMapPosPartner($userHierarchyEmpCodes);
                $finalMappingData = array_filter($finalMappingData, fn($item) => $item['id'] !== $user->id);
            }
        }

        /* ==============================
            MAIN QUERY
        ===============================*/
        DB::enableQueryLog();
        $usersQuery = User::select([
                'users.id', 'name', 'middle_name', 'last_name', 'email', 'mobile', 'username', 'employee_code', 'user_code',
                'reportingto', 'users.usertype', 'users.status', 'zone_id'
            ])
            ->with([
                'reportingToUser:id,name',
                'reportingToUser.userRoles:id,name',
                'mappedUser:id,name',
                'userType:id,name,Identifier',
                'userRoles:id,name',
                'userZoneRelation:id,office_zone',
                'lobs',
                'userQualificationRelation',
                'userAdditionalData',
                'userBranchRelation',
            ])
            ->where('users.id', '!=', 1)
            ->orderByDesc('users.id');

        /* ==============================
            FILTERS
        ===============================*/

        if ($request->filled('id')) {
            $usersQuery->where('users.id', credential_decrypt($request->id));
        }

        if ($request->filled('roleName')) {
            $usersQuery->whereHas('userRoles', fn($q) =>
                $q->where('name', $request->roleName)
            );
        }

        if ($request->filled('usertype')) {
            $usersQuery->where('usertype', $request->usertype);
        }

        if ($request->filled('user_status')) {
            $usersQuery->where('status', $request->user_status);
        }

        if ($request->filled('search')) {

            $search = credential_encrypt($request->search);

            $usersQuery->where(function ($q) use ($search) {
                $q->where('name','like',"%$search%")
                ->orWhere('email','like',"%$search%")
                ->orWhere('mobile','like',"%$search%")
                ->orWhere('username','like',"%$search%")
                ->orWhere('employee_code','like',"%$search%");
            });
        }

        if($rolecondition){
            $userTypeId = userTypes::where('Identifier', 'E')->value('id');
            if ($user->usertype == $userTypeId) {
                $finalMappingIds = array_column($finalMappingData, 'id');
                $idsToFilter = array_unique(array_merge($finalMappingIds, $userHierarchyIds));
                if ($user->is_admin !== 'Y') {
                    $usersQuery->whereIn('users.id', $idsToFilter);
                }
            } else {
                $usersQuery->whereIn('users.id', $userHierarchyIds);
            }
        }else{
            $usersQuery->whereIn('users.id', $finalMappingData);
        }
        if ($request->filled('user_status')) {
            $usersQuery->where('users.status', $request->user_status);
        }

        /* ==============================
            PAGINATION
        ===============================*/

        $perPage = $request->input('show', 10);
        
        $users = $usersQuery->paginate($perPage);
        // dd(DB::getQueryLog());

        $index = ($users->currentPage() - 1) * $users->perPage();

        $users->getCollection()->transform(function ($userItem) use(&$index, $UpdatedPospRoleConfig,$request){
            
            $assignSupervisor = ($UpdatedPospRoleConfig == 'Y' && $userItem->usertype == 2 );

                $userData = [
                'sr_no' => ++$index,
                'id' => credential_encrypt($userItem->id),
                'name' => credential_decrypt($userItem->name),
                'middle_name' => credential_decrypt($userItem->middle_name),
                'last_name' => credential_decrypt($userItem->last_name),
                'email' => credential_decrypt($userItem->email),
                'address' => credential_decrypt($userItem->address),
                'pincode' => credential_decrypt($userItem->pincode),
                'mobile' => credential_decrypt($userItem->mobile),
                'username' => credential_decrypt($userItem->username),
                'parent_username' => credential_decrypt($userItem->parent_username),
                'gender' => $userItem->gender,
                'bank_branch' => credential_decrypt($userItem->bank_branch),
                'bank_name' => credential_decrypt($userItem->bank_name),
                'bank_city' => credential_decrypt($userItem->bank_city),
                'account_no' => credential_decrypt($userItem->account_no),
                'ifsc_code' => credential_decrypt($userItem->ifsc_code),
                'account_holder_name' => credential_decrypt($userItem->account_holder_name),
                'employeeCode' => ($userItem->userType->id==1 || $userItem->userType->id==7) ? $userItem->employee_code : $userItem->user_code,
                'dob' => credential_decrypt($userItem->dob),
                'license_start_date' => credential_decrypt($userItem->license_start_date),
                'license_end_date' => credential_decrypt($userItem->license_end_date),
                'posCode' => $userItem->pos_code,
                'adhar_no' => credential_decrypt($userItem->adhar_no),
                'pan_no' => credential_decrypt($userItem->pan_no),
                'branch_id' => $userItem->userBranchRelation->first()->BranchID ?? null,
                'branch_code' => $userItem->userBranchRelation->first()->BranchCode ?? null,
                'branch_name' => $userItem->userBranchRelation->first()->BranchName ?? null,
                'department_code' => $userItem->userAdditionalData->department_code ?? null,
                'vertical_code' => $userItem->userAdditionalData->vertical_code ?? null,
                'functional_role' => $userItem->userAdditionalData->functional_role ?? null,
                'sp_code' => $userItem->userAdditionalData->sp_code ?? null,
                'Status' => $userItem->status == 'Y' ? 'Active' : 'Inactive',
                'zoneId' => [
                    'id' => $userItem->userZoneRelation->id ?? null,
                    'office_zone' => $userItem->userZoneRelation->office_zone ?? null,
                ],
                'parent_name' => $userItem->reportingToUser ? credential_decrypt($userItem->reportingToUser->name): null,
                'reportingRole' => $userItem->reportingToUser?->userRoles ? [
                    'id' => $userItem->reportingToUser?->userRoles->first()?->id,
                    'name' => $userItem->reportingToUser?->userRoles->first()?->name,
                    'model_id' => $userItem->reportingToUser?->userRoles->first()?->pivot->model_id,
                ] : null,
                'reportingTo' => $userItem->reportingToUser ? [
                    'id' => $userItem->reportingToUser->id,
                    'name' => credential_decrypt($userItem->reportingToUser->name),
                ] : null,
                'reporting_Employee_Role' => ($userItem->usertype == 1 || $userItem->usertype == 7)
                    ? [
                        'id' => $userItem->reportingToUser?->userRoles->first()->id,
                        'name' => $userItem->reportingToUser?->userRoles->first()->name,
                        'model_id' => $userItem->reportingToUser?->userRoles->first()->pivot->model_id,
                    ]
                    : ($userItem->mappedUser ? $userItem->mappedUser->role: null),
                'reporting_Employee' => ($userItem->usertype == 1 || $userItem->usertype == 7)
                    ? ($userItem->reportingToUser ? [
                        'id' => $userItem->reportingToUser->id,
                        'name' => credential_decrypt($userItem->reportingToUser->name),
                    ] : null)
                    : ($userItem->mappedUser ?  ['id' => $userItem->mappedUser->id,'name' => credential_decrypt($userItem->mappedUser->name)]: null),
                'usertype' => $userItem->userType ? [
                    'id' => $userItem->userType->id,
                    'name' => $userItem->userType->name,
                    'Identifier' => $userItem->userType->Identifier,
                ] : null,
                'role' => $userItem->userRoles->first() ? [
                    'id'   => $userItem->userRoles->first()->id,
                    'name' => $userItem->userRoles->first()->name,
                ] : null,
                'assignSupervisor' => $assignSupervisor,
            ];

            // Add lob if available
            if ($request->filled('id') && $userItem->lobs) {
                $userData['lob_id'] = $userItem->lobs->map(function ($lob) {
                    return [
                        'id' => $lob->id,
                        'name' => $lob->lob,
                        'user_id' => $lob->pivot->user_id,
                    ];
                })->values()->toArray();                
            }

            // Add qualification if available // 
            if ($request->filled('id') && $userItem->userQualificationRelation) {
                $userData['qualification'] = [
                    'id' => $userItem->userQualificationRelation->first()->qualification_master_id,
                    'name' => $userItem->userQualificationRelation->first()->qualification_name,
                ];
            }
            
            return $userData;
        });

        return response()->json([
            'status'  => true,
            'data'    => $users->items(),
            'message' => 'User listing fetched successfully.',
            'LastPage'=> $request->input('paginate') ? $users->lastPage() : '',
            'total'   => $request->input('paginate') ? $users->total() : ''
        ]);
    }


    public function userListingData(Request $request){

            $authUser = Auth::user();
 
            if ($inactiveResponse = checkUserActivity($request)) {
                return $inactiveResponse;
            }
    
            if (! $authUser->can('User Creation.view')) {
                return requestResponseMessage([
                    'status' => 403,
                    'message' => 'Access Denied'
                ]);
            }
    
           $perPage = $request->filled('show')
        ? (int) $request->show
        : 10;
    
    // HARD SAFETY LIMIT
    if ($perPage <= 0) {
        $perPage = 10;
    }
    
    if ($perPage > 50) {
        $perPage = 50;
    }
    
            $page = (int) $request->input('page', 1);
    
    
            $rolecondition = false;
            $finalMappingData = $this->userService->listRoleService();
    
            if (empty($finalMappingData)) {
                $rolecondition = true;
    
                // Materialized path based hierarchy
                $userHierarchyData = $authUser->is_admin === 'Y'
                    ? User::select('id', 'employee_code')
                        ->where('usertype', $authUser->usertype)
                        ->get()
                    : collect(getUserLowerHierarchy(
                        $authUser->id,
                        $authUser->usertype
                    ));
    
                $userHierarchyIds = $userHierarchyData->pluck('id')->toArray();
                $userHierarchyEmpCodes = $userHierarchyData->pluck('employee_code')->toArray();
                $userHierarchyEmpCodes[] = $authUser->employee_code;
    
                $userTypeIdentifier = userTypes::where('id', $authUser->usertype)
                    ->value('Identifier');
    
                if ($userTypeIdentifier === 'E' && $authUser->is_admin === 'N') {
                    $finalMappingData = getMapPosPartner($userHierarchyEmpCodes);
                    $finalMappingData = array_filter(
                        $finalMappingData,
                        fn ($item) => $item['id'] !== $authUser->id
                    );
                }
            }
    
            $usersQuery = User::select([
                    'users.id',
                    'users.name',
                    'users.middle_name',
                    'users.last_name',
                    'users.email',
                    'users.mobile',
                    'users.username',
                    'users.reportingto',
                    'users.employee_code',
                    'users.usertype',
                    'users.zone_id',
                    'users.status',
                ])
                ->where('users.username', '!=', credential_encrypt('super_admin'))
                ->where('users.usertype', '!=', 5)
                ->orderByDesc('users.id');
    
    
            if ($request->filled('id')) {
                $usersQuery->where(
                    'users.id',
                    credential_decrypt($request->id)
                );
            }
    
            if ($request->filled('usertype')) {
                $usersQuery->where('users.usertype', $request->usertype);
            }
    
            if ($request->filled('search')) {
                $search = credential_encrypt($request->search);
                $usersQuery->where(function ($q) use ($search) {
                    $q->where('users.name', 'like', "%{$search}%")
                    ->orWhere('users.email', 'like', "%{$search}%")
                    ->orWhere('users.mobile', 'like', "%{$search}%")
                    ->orWhere('users.username', 'like', "%{$search}%");
                });
            }
    
    
            if ($rolecondition) {
                if ($authUser->is_admin !== 'Y') {
                    $usersQuery->whereIn('users.id', $userHierarchyIds);
                }
            } else {
                $usersQuery->whereIn('users.id', $finalMappingData);
            }
    
            if ($request->filled('user_status')) {
                $usersQuery->where('users.status', $request->user_status);
            }
    
    
            $users = $usersQuery->paginate($perPage);
    
           
            $zoneIds = $users->pluck('zone_id')->filter()->unique();
            $zoneData = ZoneMasterModel::whereIn('id', $zoneIds)
                ->select('id', 'office_zone')
                ->get()
                ->keyBy('id');
    
            $reportingIds = $users->pluck('reportingto')->filter()->unique();
            $reportingUsers = User::whereIn('id', $reportingIds)
                ->select('id', 'name')
                ->get()
                ->keyBy('id');
    
            $userTypes = userTypes::select('id', 'name', 'Identifier')
                ->get()
                ->keyBy('id');
    
           
            $userIds = $users->pluck('id');
            $rolesByUser = DB::table('model_has_roles')
                ->join('roles', 'roles.id', '=', 'model_has_roles.role_id')
                ->where('model_has_roles.model_type', User::class)
                ->whereIn('model_has_roles.model_id', $userIds)
                ->select('model_has_roles.model_id', 'roles.id', 'roles.name')
                ->get()
                ->groupBy('model_id');
    
           
            $usersData = [];
            $index = ($users->currentPage() - 1) * $users->perPage();
    
            foreach ($users as $userItem) {
    
                $role = $rolesByUser[$userItem->id]->first() ?? null;
                $zone = $zoneData[$userItem->zone_id] ?? null;
                $reportingTo = $reportingUsers[$userItem->reportingto] ?? null;
                $usertype = $userTypes[$userItem->usertype] ?? null;
    
                $usersData[] = [
                    'sr_no' => ++$index,
                    'id' => credential_encrypt($userItem->id),
                    'name' => credential_decrypt($userItem->name).' '.credential_decrypt($userItem->middel_name).' '.credential_decrypt($userItem->last_name),
                    'mobile' => credential_decrypt($userItem->mobile),
                    'employeeCode' => $userItem->employee_code,
                    'Status' => $userItem->status == 'Y' ? 'Active' : 'Inactive',
                    'zone' => $zone ? $zone->office_zone : null,
                    'parent_name' => $reportingTo
                        ? credential_decrypt($reportingTo->name)
                        : null,
                    'usertype' => $usertype ? $usertype->name : null,
                    'role' => $role ? $role->name : null,
                ];
            }
    
    
            return response()->json([
                'status' => true,
                'data' => $usersData,
                'message' => 'User listing fetched successfully.',
                'LastPage' => $users->lastPage(),
                'total' => $users->total(),
            ]);
        
    }


    public function userHierarchyList(Request $request)
    {
        $perPage = max((int)$request->input('perPage', 10), 1);
        $keys    = (array) $request->input('keys', []);

        $userId = (int)$request->input('id') ?: auth()->id();

        if (!$userId) {
            return response()->json([
                'status'  => false,
                'data'    => [],
                'message' => 'Missing or invalid id.',
            ], 400);
        }

        $employeeCode = User::whereKey($userId)->value('employee_code');
        $allUserIds = collect([$userId]);
        $queue = [$userId];

        while (!empty($queue)) {

            $children = User::whereIn('reportingto', $queue)
                ->pluck('id')
                ->all();

            $new = array_diff($children, $allUserIds->all());

            if (!$new) break;

            $allUserIds = $allUserIds->merge($new);
            $queue = $new;
        }

        $query = User::query()
            ->where(function ($q) use ($allUserIds, $employeeCode) {
                $q->whereIn('id', $allUserIds)
                ->orWhere('employee_code', $employeeCode);
            })
            ->select([
                'id','name','middle_name','last_name','email',
                'mobile','username','reportingto',
                'employee_code','usertype','zone_id','status',
                'rm_branch_code','region_name','zone_name',
                'channel','employee_type','BRANCH_CODE',
                'CATEGORY_ID','child_pos'
            ]);

        if ($keys) {

            $query->where(function ($filter) use ($keys) {

                foreach ($keys as $k => $v) {

                    if ($v === '' || $v === null) continue;

                    $v = trim($v);
                    switch ($k) {

                        case 'Name':
                            $filter->orWhereNotNull('name');
                            break;

                        case 'Username':
                        case 'Email':
                        case 'Mobile':
                            $filter->orWhere(
                                strtolower($k),
                                credential_encrypt($v)
                            );
                            break;

                        case 'Employee Code':
                            $filter->orWhere('employee_code', 'like', "%$v%");
                            break;

                        case 'User Type':
                            $filter->orWhere('usertype', 'like', "%$v%");
                            break;

                        case 'Channel':
                            $filter->orWhere('channel', 'like', "%$v%");
                            break;

                        case 'Child POS':
                            $filter->orWhere('child_pos', $v);
                            break;

                        case 'Status':
                            $status = strtoupper(trim($v));

                            if ($status === 'ACTIVE' || $status === 'Y') {
                                $filter->orWhere('status', 'Y');
                            }

                            if ($status === 'INACTIVE' || $status === 'N') {
                                $filter->orWhere('status', 'N');
                            }

                            break;

                        case 'Zone ID':
                            $filter->orWhere('zone_id', $v);
                            break;
                    }
                }
            });
        }

        $users = $query->paginate($perPage);

        if (!empty($keys['Name'])) {

            $search = strtolower(trim($keys['Name']));

            $filtered = $users->getCollection()->filter(function ($user) use ($search) {

                $fullName = strtolower(
                    credential_decrypt($user->name) . ' ' .
                    credential_decrypt($user->middle_name) . ' ' .
                    credential_decrypt($user->last_name)
                );

                return str_contains($fullName, $search);
            });

            $users->setCollection($filtered->values());
        }

        $reportingIds = $users->pluck('reportingto')->filter()->unique();

        $reportingUsers = User::whereIn('id', $reportingIds)
            ->select('id','name','middle_name','last_name')
            ->get()
            ->keyBy('id');
        $users->getCollection()->transform(function ($user) use ($reportingUsers) {

            $user->name = trim(
                credential_decrypt($user->name).' '.
                credential_decrypt($user->middle_name).' '.
                credential_decrypt($user->last_name)
            );

            $user->email   = credential_decrypt($user->email);
            $user->mobile  = credential_decrypt($user->mobile);
            $user->username = credential_decrypt($user->username);
            // reporting manager name
            if ($user->reportingto && isset($reportingUsers[$user->reportingto])) {

                $manager = $reportingUsers[$user->reportingto];

                $user->reportingto = trim(
                    credential_decrypt($manager->name).' '.
                    credential_decrypt($manager->middle_name).' '.
                    credential_decrypt($manager->last_name)
                );

            } else {
                $user->reportingto = null;
            }

            unset($user->middle_name, $user->last_name);
            return $user;
        });

        $users->getCollection()->transform(function ($user) {
            if ($user->status == 'Y') {
                $user->status = 'Active';
            } else {
                $user->status = 'Inactive';
            }

            return $user;
        });

        return response()->json([
            'pagination' => [
                'total_records' => $users->total(),   
                'per_page'      => $users->perPage(),
                'current_page'  => $users->currentPage(),
                'total_pages'   => $users->lastPage(),
            ],
            'status'  => true,
            'data'    => $users->items(),
            'message' => 'User hierarchy listing fetched successfully.',
        ]);
    }

    public function activeInactiveUser(Request $request)
    {
        $request->validate([
            'mobile' => 'required',
            'status' => 'required|in:Y,N',
        ]);

        $user = User::where('mobile', credential_encrypt($request->mobile))->first();

        if ($user) {
            $user->status = $request->status;
            $user->save();

            return response()->json([
                'status' => 200,
                'message' => 'Status updated successfully'
            ]);
        }

        return response()->json([
            'status' => 500,
            'message' => 'User not found'
        ]);
    }
}
