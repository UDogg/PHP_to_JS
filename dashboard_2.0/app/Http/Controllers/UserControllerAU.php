<?php

namespace App\Http\Controllers;

use App\Http\Requests\UserBankDetailsReq;
use App\Imports\AUBranchImport;
use App\Imports\HierarchyAUImport;
use App\Imports\UserAUImport;
use App\Models\AuBranch;
use App\Models\AUHierarchyDump;
use App\Models\lobMaster;
use App\Models\QualificationMaster;
use App\Models\Role;
use App\Models\SellNow;
use App\Models\User;
use App\Models\UserActivateLog;
use App\Models\UserAdditionalData;
use App\Models\UserDeactivateCounter;
use App\Models\UserMapping;
use App\Models\userTypes;
use App\Models\ZoneMasterModel;
use Carbon\Carbon;
use Exception;
use Illuminate\Http\Request;
use Illuminate\Pagination\LengthAwarePaginator;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\Validator;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;
use MongoDB\Operation\Update;

class UserControllerAU extends Controller
{
    protected $authenticatedUser;

    protected $userRoleMapping;

    protected $UserlobMapping;

    public function __construct(Auth $auth, RolesController $rolecontroller, SellNowController $sellNowController)
    {
        $this->authenticatedUser = $auth::user();
        $this->userRoleMapping = $rolecontroller;
        $this->UserlobMapping = $sellNowController;
    }

    public function UserBankDetails(UserBankDetailsReq $request, int $id)
    {

        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->authenticatedUser->can($permission)) {

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

            return requestResponseMessage(['status' => 200, 'message' => 'User Updated Successfully', 'data' => [
                'email' => $request->email,
                'userId' => $userId,
            ]]);
        } else {
            return requestResponseMessage(['status' => 403, 'message' => 'Error While Updating User.']);
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

        $rules = [
            'UserID' => 'required|string',
            'Name' => 'required|string',
            'MobileNumber' => 'required|regex:/^[0-9]{10}$/',
            'EmailID' => 'required|email',
            // 'gender' => 'required|string|in:M,F',
            // 'address' => 'required|string',
            // 'pincode' => 'required|digits:6',
            'Status' => 'required|in:0,1',
            // 'user_type' => 'required|integer',
            // 'RoleID' => 'required|integer',
            // 'lob_id' => 'required|array',
            'BranchCode' => 'required|array',
            // 'qualification' => 'required|integer',
            // 'dob' => 'required|date_format:d/m/Y',
            // 'reportingRole' => 'required|integer',
            'ReportingTo' => 'required|integer',
            'EmployeeCode' => 'required',
            'SPCode' => 'required_if:IsSP,Y|required_if:IsSP,1',

        ];

        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            logApiRequestResponse(
                'syncUsers',
                'POST',
                $request->all(),
                ['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()],
                400,
                '',
                'au-user-sync'
            );

            return response()->json(['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()], 400);
        }

        $reportingEmployeeCode = $request->EmployeeCode;
        if ($request->SellerType == 'P') {
            $request->merge(['user_type' => 3]);
        }else{
            if($request->IsSP=='Y'){
                $request->merge(['user_type' => 7]);    
            }else{
                $request->merge(['user_type' => 1]);
            }
        }
        if($request->ReportingTo!='0' && $request->ReportingTo!=''){
            $reportingToData = User::where('username', credential_encrypt($request->ReportingTo))->first();
            if(! $reportingToData){
                logApiRequestResponse(
                    'syncUsers',
                    'POST',
                    $request->all(),
                    ['status' => 400, 'message' => 'User with reportingTo Employee Code $request->ReportingTo does not exists'],
                    200,
                    '',
                    'au-user-sync'
                );

                return requestResponseMessage(['status' => 400, 'message' => 'User with reportingTo Employee Code $request->ReportingTo does not exists']);
            }
            if ($request->SellerType == 'P') {
                if ($reportingToData->usertype == 3) {
                    $reportingTo = $reportingToData->id;
                } else {
                    $reportingEmployeeCode = $request->ReportingTo;
                    $reportingTo = User::where('usertype', $request->user_type)->where('is_admin', 'Y')->pluck('id')->first();
                }
            } else {
                if ($reportingToData) {
                    $reportingTo = $reportingToData->id;
                } else {
                    $reportingTo = User::where('usertype', $request->user_type)->where('is_admin', 'Y')->pluck('id')->first();
                }
            }
        }else{
            $reportingTo = User::where('usertype', $request->user_type)->where('is_admin', 'Y')->pluck('id')->first();
        }
        

        DB::beginTransaction();
        try {
            $qrCode_generated = generateQrcode();
            $secret = $qrCode_generated['secret'];
            $totp_secret = credential_encrypt($secret);

            $password = generateRandomPassword(8);

            $name = trim($request->Name);
            $name = preg_replace('/\b(mr|mrs|ms|miss|dr)\.?/i', '', $name);
            $name = trim(preg_replace('/\s+/', ' ', $name));
            $parts = explode(' ', $name);
            $firstName = $parts[0];
            $lastName = count($parts) > 1 ? array_pop($parts) : '';
            $middleName = count($parts) > 1 ? implode(' ', array_slice($parts, 1)) : '';

            $inserted = User::updateOrCreate(
                ['username' => credential_encrypt($request->UserID)], 
                ['name' => credential_encrypt($firstName),
                'middle_name' => credential_encrypt($middleName),
                'last_name' => credential_encrypt($lastName),
                'email' => credential_encrypt($request->EmailID),
                'mobile' => credential_encrypt($request->MobileNumber),
                'gender' => ($request->Gender),
                'address' => credential_encrypt($request->Address),
                'pincode' => credential_encrypt($request->Pincode),
                'password' => Hash::make($password),
                'totp_secret' => $totp_secret,
                'employee_code' => $reportingEmployeeCode,
                'status' => $request->Status,
                'usertype' => $request->user_type,
                'zone_id' => 1,
                'reportingto' => $reportingTo,
                'pan_no' => credential_encrypt($request->PanNo),
                // 'adhar_no' => credential_encrypt($request->adhar_no),
                // 'qualification' => $request->qualification,
                'dob' => credential_encrypt($request->DOB),
                // 'license_start_date' => credential_encrypt($request->license_start_date),
                // 'license_end_date' => credential_encrypt($request->license_end_date),
                // 'pos_code' => $userCode,
                // 'oemId' => $request->oemId,
                // 'mispId' => $request->mispId,
                // 'branchId' => $request->branchId,
                'user_code' => $request->EmployeeCode,
            ]);

            if ($inserted) {
                $user_id = $inserted->id;


                $date_of_joining = $request->filled('DateOfJoining') ? Carbon::parse($request->DateOfJoining)->endOfDay() : null;
                $date_of_leaving = $request->filled('DateOfLeaving') ? Carbon::parse(trim($request->DateOfLeaving))->endOfDay() : null;
                $certificate_valid_from = $request->filled('CertificateValidFrom') ? Carbon::parse(trim($request->CertificateValidFrom))->startOfDay() : null;
                $certificate_valid_till = $request->filled('CertificateValidTill') ? Carbon::parse(trim($request->CertificateValidTill))->endOfDay() : null;

                $inserted = UserAdditionalData::updateOrCreate(
                    ['user_id' => $user_id,],[
                    'job_id' => $request->JobID,
                    'date_of_joining' => $date_of_joining,
                    'date_of_leaving' => $date_of_leaving,
                    'role_id' => $request->RoleID,
                    'L1_user_id' => $request->L1ID,
                    'L2_user_id' => $request->L2ID,
                    'L3_user_id' => $request->L3ID,
                    'RBM' => $request->RBM,
                    'CBM' => $request->CBM,
                    'department_code' => $request->DepartmentCode,
                    'vertical_code' => $request->VerticalCode,
                    'functional_role' => $request->FunctionalRole,
                    'user_salary' => $request->UserSalary,
                    'is_sp' => $request->IsSP == '1' ? 'Y' : 'N',
                    'sp_name' => $request->name,
                    'sp_code' => $request->SPCode,
                    'sp_type' => $request->SPType,
                    'noc_issued' => $request->NOCIssued,
                    'sp_certificate_date' => $request->SPCertificateDate,
                    'certificate_valid_from' => $certificate_valid_from,
                    'certificate_valid_till' => $certificate_valid_till,
                ]);

                $branch_id = DB::table('au_branch_dump')->whereIn('BranchCode', $request->BranchCode)->pluck('BranchID');

                foreach ($branch_id as $branch_value) {
                    DB::table('user_branch_relation')
                        ->where('user_id', $user_id)
                        ->delete();

                    $inserted = DB::table('user_branch_relation')->insert([
                        'user_id' => $user_id,
                        'branch_id' => $branch_value,
                    ]);
                }

                $user_role_id = AUHierarchyDump::where('id', $request->RoleID)->first()->role_id;
                $user_role_id = $request->IsSP === 'Y' ? 12 : ($request->SellerType === 'P' ? 7 : 13);

                $request->merge(['user_id' => $user_id, 'role_id' => $user_role_id]);

                $userrolemapping = $this->userRoleMapping->UserRoleMapping($request);

                $lob_ids = lobMaster::where('is_enabled', 'Y')->pluck('id');

                SellNow::where('user_id', $user_id)->delete();

                foreach ($lob_ids as $value) {

                    $userlobMapping = SellNow::create([
                        'user_id' => $user_id,
                        'lob_id' => $value,
                        'created_at' => Carbon::now(),
                        'updated_at' => null,
                    ]);
                }

                if (! $userlobMapping) {
                    return response()->json([
                        'status' => 400,
                        'message' => 'Error While Mapping lob to User.',
                    ]);
                }

                DB::commit();
                logApiRequestResponse(
                    'syncUsers',
                    'POST',
                    $request->all(),
                    ['status' => 200, 'message' => 'User Created Successfully', 'data' => [
                        'userId' => $user_id,
                    ]],
                    200,
                    '',
                    'au-user-sync'
                );

                return requestResponseMessage(['status' => 200, 'message' => 'User Created or Updated Successfully', 'data' => [
                    'userId' => $user_id,
                ]]);

            } else {
                DB::rollBack();
                logApiRequestResponse(
                    'syncUsers',
                    'POST',
                    $request->all(),
                    ['status' => 400, 'message' => 'Error While Creating User.'],
                    200,
                    '',
                    'au-user-sync'
                );

                return requestResponseMessage(['status' => 400, 'message' => 'Error While Creating User.']);
            }
        } catch (\Exception $e) {
            DB::rollBack();
            logApiRequestResponse(
                'syncUsers',
                'POST',
                $request->all(),
                ['status' => 400, 'message' => 'Something went wrong: '.$e->getMessage()],
                200,
                '',
                'au-user-sync'
            );

            return requestResponseMessage(['status' => 400, 'message' => 'Something went wrong: '.$e->getMessage()]);
        }
    }

    public function importUserExcel(Request $request)
    {
        set_time_limit(0);
        ini_set('memory_limit','-1');

        $request->validate([
            'file' => 'required|mimes:xlsx,csv,xls',
        ]);

        $rolecontroller = new RolesController($request);
        $sellNowController = new SellNowController;
        $auth = Auth::user();

        try {
            Excel::import(new UserAUImport($request, $auth, $rolecontroller, $sellNowController), $request->file('file'));

            return response()->json([
                'message' => 'User data imported successfully',
            ], 200);
        } catch (\Exception $e) {

            return requestResponseMessage(['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()]);
        }
    }

    public function updateUserRoles(Request $request)
    {
        User::join('user_additional_data','users.id','user_additional_data.user_id')->where('users.id','>',5)->chunk(1000, function ($rows) use ($request) {

            foreach ($rows as $row) {

                $user_role_id = AUHierarchyDump::where('department_code', $row->department_code)
                    ->where('vertical_code', $row->vertical_code)
                    ->where(function ($q) use ($row) {
                        $q->where('job_id', $row->job_id)
                        ->orWhereNull('job_id');
                    })
                    ->orderByRaw('job_id IS NULL')->first()->role_id ?? null;
                    // ->value('role_id');

                $user_role_id = $row->sp_code
                    ? 12
                    : ($user_role_id ? $user_role_id : 24);

                $requestData = new Request([
                    'user_id' => $row->user_id,
                    'role_id' => $user_role_id
                ]);

                $this->userRoleMapping->UserRoleMapping($requestData);
            }
        });
        return response()->json([
            'message' => 'User data imported successfully',
        ], 200);

    }


    public function importAUUsers(Request $request)
    {
        $au_user_dump = DB::table('au_user_dump')->where('ImportedStatus', 0)->limit(1000)->get();

        foreach ($au_user_dump as $auValue) {
            $reportingToData = User::where('username', credential_encrypt($auValue->ReportingTo))->first();

            if ($reportingToData) {
                $reportingTo = $reportingToData->id;
            } else {
                $reportingTo = 0;
            }

            DB::beginTransaction();
            try {
                $qrCode_generated = generateQrcode();
                $secret = $qrCode_generated['secret'];
                $totp_secret = credential_encrypt($secret);

                $password = 'Admin@123';

                $inserted = User::updateOrCreate([
                    'username' => credential_encrypt($auValue->UserLoginID),
                    'name' => credential_encrypt($auValue->UserName),
                    // 'middle_name' => credential_encrypt($auValue->middle_name),
                    // 'last_name' => credential_encrypt($auValue->last_name),
                    'email' => credential_encrypt($auValue->EmailID),
                    'mobile' => credential_encrypt($auValue->MobileNo),
                    'gender' => ($auValue->Gender),
                    'address' => credential_encrypt($auValue->Address),
                    'pincode' => credential_encrypt($auValue->Pincode),
                    'password' => Hash::make($password),
                    'totp_secret' => $totp_secret,
                    'employee_code' => $auValue->CompanyEmployeeID,
                    'status' => $auValue->IsActive,
                    'usertype' => 1, // $auValue->user_type,
                    // 'zone_id' => $auValue->zoneId,
                    'reportingto' => $reportingTo,
                    'pan_no' => credential_encrypt($auValue->PanNo),
                    // 'adhar_no' => credential_encrypt($auValue->adhar_no),
                    // 'qualification' => $auValue->qualification,
                    'dob' => credential_encrypt($auValue->DOB),
                    // 'license_start_date' => credential_encrypt($auValue->license_start_date),
                    // 'license_end_date' => credential_encrypt($auValue->license_end_date),
                    // 'pos_code' => $userCode,
                    // 'oemId' => $auValue->oemId,
                    // 'mispId' => $auValue->mispId,
                    // 'branchId' => $auValue->branchId,
                ]);
                if ($inserted) {
                    $user_id = $inserted->id;

                    $inserted = UserAdditionalData::updateOrCreate([
                        'user_id' => $user_id,
                        'job_id' => $auValue->JobID,
                        'branch_code' => $auValue->BranchCode,
                        'date_of_joining' => $auValue->DateOfJoining,
                        'date_of_leaving' => $auValue->DateOfLeaving,
                        'role_id' => $auValue->FkRoleID,
                        'L1_user_mobile' => $auValue->L1MobileNo,
                        'L1_user_email' => $auValue->L1EmailID,
                        'L1_user_id' => $auValue->L1Name,
                        'L2_user_id' => $auValue->L2ID,
                        'L3_user_id' => $auValue->L3ID,
                        'department_code' => $auValue->DepartmentCode,
                        'vertical_code' => $auValue->VerticalID,
                        'functional_role' => $auValue->FkRoleID,
                        'user_salary' => $auValue->UserSalary,
                        // 'is_sp' => $auValue->IsSP,
                        // 'sp_code' => $auValue->SPCode,
                        // 'sp_type' => $auValue->SPType,
                        // 'noc_issued' => $auValue->NOCIssued,
                        // 'sp_certificate_date' => $auValue->SPCertificateDate,
                        // 'certificate_valid_from' => $auValue->CertificateValidFrom,
                        // 'certificate_valid_till' => $auValue->CertificateValidTill,
                    ]);
                    $role_id = $auValue->FkRoleID ?? 1;

                    $request->merge(['user_id' => $user_id, 'role_id' => $role_id]);

                    $userrolemapping = $this->userRoleMapping->UserRoleMapping($request);

                    DB::table('au_user_dump')
                        ->where('BackOfficeUserID', $auValue->BackOfficeUserID)
                        ->update(['ImportedStatus' => 1]);

                    DB::commit();

                } else {
                    DB::rollBack();

                }
            } catch (\Exception $e) {
                DB::rollBack();

                return requestResponseMessage(['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()]);
            }
        }

        return requestResponseMessage(['status' => 200, 'message' => 'User Imported Successfully']);

    }

    protected function prepareUserData(array $data, $reportingEmployeeCode, $userCurrentData)
    {
        $userData = [
            'name' => credential_encrypt($data['name']),
            'middle_name' => credential_encrypt($data['middle_name'] ?? null),
            'last_name' => credential_encrypt($data['last_name'] ?? null),
            'email' => credential_encrypt($data['email'] ?? null),
            'mobile' => credential_encrypt($data['mobile']),
            'gender' => $data['gender'] ?? null,
            'address' => credential_encrypt($data['address'] ?? null),
            'pincode' => credential_encrypt($data['pincode'] ?? null),
            'password' => Hash::make('pass@123'),
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
        $this->UserMapUsertype($getUser->id, $getUser->usertype, $data['role_id'], $getUser->reportingto, $getUser->employee_code);

        return response()->json([
            'status' => 200,
            'message' => 'User Mapping Created  Successfully',
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
        if (! $this->authenticatedUser->can($permission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $getusertype = userTypes::select('name', 'Identifier')->where('id', $request->user_type)->where('is_active', 'Y')->first();
        $userCode = '';

        if ($getusertype->Identifier == 'E' || $getusertype->Identifier == 'SP') {
            $validate = $request->validate([
                'employeeCode' => 'required|string',
            ]);

            $employeeExists = User::where('employee_code', $request->employeeCode)
                ->where('id', '!=', credential_decrypt($request->id))
                ->exists();

            $mobileExists = User::where('mobile', credential_encrypt($request->mobile))
                ->where('id', '!=', credential_decrypt($request->id))
                ->exists();

            if ($employeeExists) {
                return response()->json(['message' => 'The employee code already exists for another user.'], 400);
            }
            if ($mobileExists) {
                return response()->json(['message' => 'The mobile number already exists for another user.'], 400);
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
                'pan_no' => 'required|regex:/^[A-Z]{5}[0-9]{4}[A-Z]$/',
            ]);
            $userCode = $request->posCode;
            $reportingEmployeeCode = $this->getPosReportingEmployeeCode($request->reportingEmployee);
        }
        if ($getusertype->Identifier == 'Partner') {
            // $reportingEmployeeCode = $this->getPosReportingEmployeeCode($request->reportingTo);
            $reportingEmployeeCode = $request->employeeCode ?? 0;
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

        $mapRepotingId = $request->reportingTo;
        if ($getusertype->Identifier != 'E' && $getusertype->Identifier != 'SP') {

            $getReportingUser = User::find($request->reportingTo);
            if ($getReportingUser && $request->user_type !== $getReportingUser->user_type) {
                $mapRepotingId = User::where('is_admin', 'Y')
                    ->where('usertype', $request->user_type)
                    ->value('id') ?? 0;
            }

            if ($request->employeeCode == '0') {

                $mapemployeeCode = User::select('employee_code')->where('id', $request->reportingTo)->first()['employee_code'] ?? 0;
                $request->merge([
                    'employeeCode' => $mapemployeeCode,
                ]);
            }

        }
        $updated = $user->update([
            'username' => credential_encrypt($request->mobile),
            'name' => credential_encrypt($request->name),
            'middle_name' => credential_encrypt($request->middle_name),
            'last_name' => credential_encrypt($request->last_name),
            'email' => credential_encrypt($request->email),
            'mobile' => credential_encrypt($request->mobile),
            'gender' => $request->gender,
            'address' => credential_encrypt($request->address),
            'pincode' => credential_encrypt($request->pincode),
            //            'password' => Hash::make($password),
            'totp_secret' => $totp_secret,
            'status' => $request->status,
            'usertype' => $request->user_type,
            'zone_id' => $request->zoneId,
            'reportingto' => $mapRepotingId,
            'employee_code' => $request->employeeCode ?? '',
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
                'role_id' => $request->role_id,
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

        if (! $userlobMapping) {
            return response()->json([
                'status' => 400,
                'message' => 'Error While Mapping lob to User.',
            ]);
        }

        if ($updated) {
            return requestResponseMessage(['status' => 200, 'message' => 'User Updated Successfully', 'data' => ['email' => $request->email]]);
        } else {
            return requestResponseMessage(['status' => 404, 'message' => 'Error While Updating User.']);
        }
    }

    public function userListing(Request $request)
    {
        $user = Auth::user();
        if ($inactiveResponse = checkUserActivity($request)) {
            return $inactiveResponse;
        }

        $userListingPermission = 'User Creation.view';
        if (! $user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $rolecondition = false;
        $finalMappingData = [];
        $finalMappingData = $this->userService->listRoleService();
        if (empty($finalMappingData)) {
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
                $finalMappingData = array_filter($finalMappingData, fn ($item) => $item['id'] !== $user->id);
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
            'users.qualification', 'users.profile_image',
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
                    ->orWhere('users.last_name', 'like', "%{$search}%");
            });
        }
        if ($rolecondition) {
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
        } else {
            $usersQuery->whereIn('users.id', $finalMappingData);
        }
        if ($request->filled('user_status')) {
            $usersQuery->where('users.status', $request->user_status);
        }

        $perPage = $request->input('show', 10);
        $users = $request->input('paginate') === 'true'
            ? $usersQuery->paginate($perPage)
            : $usersQuery->get();

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

            $assignSupervisor = ($UpdatedPospRoleConfig == 'Y' && $userItem->usertype == 2);
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
                'employeeCode' => $userItem->usertype == 1 ? $userItem->employee_code : null,
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
                'parent_name' => $reportingTo ? credential_decrypt($reportingTo->name) : null,
                'reportingRole' => $reportingRole,
                'reportingTo' => $reportingTo ? [
                    'id' => $reportingTo->id,
                    'name' => credential_decrypt($reportingTo->name),
                ] : null,
                'reporting_Employee_Role' => $userItem->usertype == 1
                    ? $reportingRole
                    : ($reportingToRoleEmployee ? $reportingToRoleEmployee : null),
                'reporting_Employee' => $userItem->usertype == 1
                    ? ($reportingTo ? [
                        'id' => $reportingTo->id,
                        'name' => credential_decrypt($reportingTo->name),
                    ] : null)
                    : ($reportingToEmployee ? ['id' => $reportingToEmployee->id, 'name' => credential_decrypt($reportingToEmployee->name)] : null),
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
            'LastPage' => $request->input('paginate') ? $users->lastPage() : '',
            'total' => $request->input('paginate') ? $users->total() : '',
        ]);
    }

    private function UserMapUsertype($userId, $usertype, $role_id, $reportingTo, $employee_code = '')
    {
        //  $user = Auth::user();
        //  $userListingPermission = 'User Creation.view';
        // if (!$user->can($userListingPermission)) {
        //     return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        // }
        $checkInMappings = UserMapping::where('user_id', $userId)->where('user_type', $usertype)->first();
        if ($checkInMappings) {
            return requestResponseMessage(['status' => 400, 'message' => 'User  Already Exists please Try with other email username and mobile number']);
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
        if (! $user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $size = $request->input('size', 10);
        $pageNo = $request->input('page', 1);
        $data = User::select('id', 'name', 'middle_name', 'last_name', 'email', 'usertype', 'mobile', 'username')
            ->where('usertype', getUserTypeIdByIdentifier('U'))
            ->paginate($size);

        $customerData = $data->map(function ($customer, $index) use ($request, $size, $pageNo) {

            $decrypted = [
                'sr_no' => $pageNo * $size - $size + ($index + 1),
                'name' => credential_decrypt($customer->name),
                'email' => credential_decrypt($customer->email),
                'mobile' => credential_decrypt($customer->mobile),
                'username' => credential_decrypt($customer->username),
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

        if ($request->has('search_value') && ! empty($request->search_value)) {
            $customerData = $customerData->filter(function ($item) use ($request) {
                return stripos($item['name'], $request->search_value) !== false ||
                stripos($item['email'], $request->search_value) !== false ||
                stripos($item['mobile'], $request->search_value) !== false;
            })->values();
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                ['header' => 'Sr No', 'accessorKey' => 'sr_no', 'isActions' => 'integer'],
                // ["header" => "ID", "accessorKey" => "id", "isActions" => 'integer'],
                ['header' => 'Name', 'accessorKey' => 'name', 'isActions' => 'string'],
                ['header' => 'Middle Name', 'accessorKey' => 'middle_name', 'isActions' => 'string'],
                ['header' => 'Last Name', 'accessorKey' => 'last_name', 'isActions' => 'string'],
                ['header' => 'Email', 'accessorKey' => 'email', 'isActions' => 'string'],
                ['header' => 'Mobile', 'accessorKey' => 'mobile', 'isActions' => 'string'],
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
        if (! $user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $validatedData = $request->validate([
            'user_id' => 'required', // exists:users,id
            'b2c' => 'boolean',
            'userCreation' => 'boolean',
            'employee' => 'boolean',
            'pos' => 'boolean',
            'partner' => 'boolean',
        ]);

        $user = User::find(credential_decrypt($validatedData['user_id']));

        if (! $user) {
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

        $user->update([
            'is_b2cflag' => $is_b2c_flag,
            // 'userCreation' => $user_creation_flag,
            'data_flag' => implode(',', $dataFlag),
        ]);

        return response()->json(['status' => 200, 'message' => 'User access updated successfully'], 200);

    }

    public function prefillManageAccessData(Request $request)
    {
        $user = Auth::user();
        $userListingPermission = 'User Creation.view';
        if (! $user->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        $user = User::find(credential_decrypt($request['user_id']));

        if (! $user) {
            return response()->json(['status' => 404, 'message' => 'User not found'], 404);
        }

        $dataFlagArray = explode(',', $user->data_flag ?? '');

        $responseData = [
            'b2c' => (bool) $user->is_b2cflag,
            'userCreation' => false,
            'employee' => in_array('E', $dataFlagArray),
            'pos' => in_array('P', $dataFlagArray),
            'partner' => in_array('Partner', $dataFlagArray),
        ];

        return response()->json([
            'status' => 200,
            'return_data' => $responseData,
        ], 200);
    }

    public function passwordUpdate(Request $request)
    {
        $userListingPermission = 'User Creation.view';
        if (! $this->authenticatedUser->can($userListingPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $rules = [
            'old_password' => 'required|string',
            'password' => [
                'required',
                'string',
                'min:8',
                'regex:/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/',
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
                'status' => 400,
                'return_data' => [],
                'message' => 'Validation fails',
                'errors' => $validator->errors(),
            ], 400);
        }

        $user = Auth::user();

        if (! Hash::check($request->old_password, $user->password)) {
            return response()->json([
                'status' => false,
                'message' => 'Old password does not match.',
            ], 401);
        }

        if ($request->old_password === $request->password) {
            return response()->json([
                'status' => false,
                'message' => 'old password and new password cannot be same change your new password.',
            ], 401);
        }

        $check = User::where('id', $user->id)->update([
            'password' => Hash::make($request->password),
        ]);

        if ($check) {
            return response()->json([
                'status' => true,
                'message' => 'Password updated successfully.',
            ], 200);
        } else {
            return response()->json([
                'status' => false,
                'message' => 'Password updated failed.',
            ], 400);
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
                'errors' => $validator->errors(),
            ], 422);
        }

        $mobile = $request->input('mobile');

        $userExists = User::where('mobile', credential_encrypt($mobile))->exists();

        if ($userExists) {
            return response()->json([
                'status' => true,
                'mobile' => $mobile,
                'exists' => $userExists,
                'message' => $userExists ? 'Mobile number already exists.' : 'Mobile number is available.',
            ], 200);
        } else {
            return response()->json([
                'status' => false,
                'mobile' => $mobile,
                'exists' => $userExists,
                'message' => $userExists ? 'Mobile number already exists.' : 'Mobile number is available.',
            ], 200);
        }

    }

    public function employeeSPTagging(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'UserID' => 'required',
            'SPName' => 'required',
            'SPCode' => 'required',
            'SPCertificateDate' => 'required',
            'CertificateValidFrom' => 'required',
            'CertificateValidTill' => 'required',
        ]);

        if ($validator->fails()) {
            logApiRequestResponse(
                'employeeSPTagging',
                'POST',
                $request->all(),
                ['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()],
                400,
                '',
                'au-emp-sp-tagging'
            );

            return response()->json([
                'status' => 422,
                'errors' => $validator->errors(),
            ]);
        }

        $userSPDetails = User::where('username', credential_encrypt($request->UserID))->first();
        $sp_role = Role::where('name', 'SP')->first();
        $sp_user_type = userTypes::where('name', 'SP')->first();

        if (! empty($userSPDetails)) {

            $certificate_valid_from = $request->filled('CertificateValidFrom') ? Carbon::parse(trim($request->CertificateValidFrom))->startOfDay() : null;
            $certificate_valid_till = $request->filled('CertificateValidTill') ? Carbon::parse(trim($request->CertificateValidTill))->endOfDay() : null;

            $updated = UserAdditionalData::updateOrCreate(
                ['user_id' => $userSPDetails->id],
                [
                    'sp_name' => $request->SPName,
                    'is_sp' => 'Y',
                    'sp_type' => $request->SPType,
                    'sp_code' => $request->SPCode,
                    'sp_urnno' => $request->SPUrnNo,
                    'noc_issued' => $request->NOCIssued,
                    'sp_certificate_date' => $request->SPCertificateDate,
                    'certificate_valid_from' => $certificate_valid_from,
                    'certificate_valid_till' => $certificate_valid_till,
                ]);

            $userSPDetails->userType = $sp_user_type->id;
            $userSPDetails->save();

            $request->merge(['user_id' => $userSPDetails->id, 'role_id' => $sp_role->id]);
            $userrolemapping = $this->userRoleMapping->UserRoleMapping($request);
            logApiRequestResponse(
                'employeeSPTagging',
                'POST',
                $request->all(),
                ['status' => 200, 'message' => 'SP tagging created successfully', 'data' => [
                    'userId' => $userSPDetails->id,
                ]],
                200,
                '',
                'au-emp-sp-tagging'
            );

            return response()->json(['status' => 200, 'message' => 'SP tagging created successfully'], 200);
        } else {
            logApiRequestResponse(
                'employeeSPTagging',
                'POST',
                $request->all(),
                ['status' => 200, 'message' => 'User details not found'],
                200,
                '',
                'au-emp-sp-tagging'
            );
            return response()->json(['status' => 200, 'message' => 'User details not found'], 400);
        }
    }

    public function syncBranch(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'BranchID' => 'required|integer',
            'BranchCode' => 'required|string|max:50',
            'BranchName' => 'required|string|max:255',
            'Circle' => 'nullable|string|max:100',
            'Zone' => 'nullable|string|max:100',
            'Region' => 'nullable|string|max:100',
            'Cluster' => 'nullable|string|max:100',
            'State' => 'nullable|string|max:100',
            'City' => 'nullable|string|max:150',
            'Pincode' => 'nullable|string|max:10',
            'Branch_Address' => 'nullable|string',
            'Status' => 'nullable|integer',
        ]);

        if ($validator->fails()) {
            logApiRequestResponse(
                'syncBranch',
                'POST',
                $request->all(),
                ['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()],
                400,
                '',
                'au-sync-branch'
            );

            return response()->json([
                'status' => false,
                'message' => 'Validation Error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        try {
            // Insert or update
            AuBranch::updateOrInsert(
                ['BranchID' => $request->BranchID],
                [
                    'BranchCode' => $request->BranchCode,
                    'BranchName' => $request->BranchName,
                    'Circle' => $request->Circle,
                    'Zone' => $request->Zone,
                    'Region' => $request->Region,
                    'Cluster' => $request->Cluster,
                    'State' => $request->State,
                    'City' => $request->City,
                    'Pincode' => $request->Pincode,
                    'Branch_Address' => $request->Branch_Address,
                    'Status' => $request->Status,
                ]
            );
            logApiRequestResponse(
                'syncBranch',
                'POST',
                $request->all(),
                ['status' => 200, 'message' => 'Branch synced successfully', 'data' => [
                    'BranchID' => $request->BranchID,
                ]],
                200,
                '',
                'au-sync-branch'
            );

            return response()->json(['status' => 200, 'message' => 'Branch synced successfully'], 200);

        } catch (\Exception $e) {
            logApiRequestResponse(
                'syncBranch',
                'POST',
                $request->all(),
                ['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()],
                200,
                '',
                'au-sync-branch'
            );

            return response()->json([
                'success' => false,
                'message' => 'Error: '.$e->getMessage(),
            ], 400);
        }
    }

    public function syncDesignation(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'ID' => 'required|integer',
            'Designation' => 'required|string',
            'JobID' => 'nullable|string',
            'JobFamily' => 'nullable|string',
            'DepartmentName' => 'nullable|string',
            'DepartmentCode' => 'nullable|string',
            'VerticalName' => 'nullable|string',
            'VerticalCode' => 'nullable|string',
            'BU' => 'nullable|string',
            'MISID' => 'nullable|string',
            'RoleID' => 'nullable|integer',
            'ReportRoleType' => 'nullable|string',
        ]);

        if ($validator->fails()) {
            logApiRequestResponse(
                'syncDesignation',
                'POST',
                $request->all(),
                ['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()],
                400,
                '',
                'au-sync-designation'
            );

            return response()->json([
                'status' => false,
                'message' => 'Validation Error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        try {
            // Insert or update
            AUHierarchyDump::updateOrCreate(
                ['id' => $request->ID],
                [
                    'designation' => $request->Designation,
                    'job_id' => $request->JobID,
                    'job_family' => $request->JobFamily,
                    'department_name' => $request->DepartmentName,
                    'department_code' => $request->DepartmentCode,
                    'vertical_name' => $request->VerticalName,
                    'vertical_code' => $request->VerticalCode,
                    'bu' => $request->BU,
                    'branch_category_id' => $request->BranchCategoryId,
                    'misid' => $request->MISID,
                    'role_id' => $request->RoleID,
                    'report_role_type' => $request->ReportRoleType,
                ]
            );
            logApiRequestResponse(
                'syncDesignation',
                'POST',
                $request->all(),
                ['status' => 200, 'message' => 'Designation synced successfully', 'data' => [
                    'ID' => $request->ID,
                ]],
                200,
                '',
                'au-sync-designation'
            );

            return response()->json(['status' => 200, 'message' => 'Designation synced successfully'], 200);

        } catch (\Exception $e) {
            logApiRequestResponse(
                'syncDesignation',
                'POST',
                $request->all(),
                ['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()],
                200,
                '',
                'au-sync-designation'
            );

            return response()->json([
                'success' => false,
                'message' => 'Error: '.$e->getMessage(),
            ], 400);
        }
    }

    public function importHierarchy(Request $request)
    {
        $request->validate([
            'file' => 'required|mimes:xlsx,xls,csv',
        ]);

        try {
            Excel::import(new DesignationsImport, $request->file('file'));

            return response()->json([
                'success' => true,
                'message' => 'Designations imported successfully.',
            ]);
        } catch (\Exception $e) {
            return response()->json([
                'success' => false,
                'message' => 'Import failed: '.$e->getMessage(),
            ], 400);
        }
    }

    public function listDocuments(Request $request)
    {
        try {
            $api = credential_decrypt(config('listDocuments.api'));
            if (empty($api)) {
                return response()->json([
                    'status' => false,
                    'message' => 'API URL not configured.',
                ], 400);
            }
            $payload = [];
            if (! empty($request->from) && ! empty($request->to)) {
                $payload['form'] = $request->from;
                $payload['to'] = $request->to;
            }
            if (! empty($request->vehicle_registration_no)) {
                $payload['vehicle_registration_no'] = $request->vehicle_registration_no;
            }
            if (! empty($request->id)) {
                $payload['id'] = $request->id;
            }
            if ($request->status) {
                $payload['status'] = $request->status;
            } else {
                $payload['status'] = 'rejected';
            }
            if ($request->pending_status) {
                $payload['status'] = 'pending';
            }
            if ($request->per_page) {
                $payload['per_page'] = $request->per_page;
            }
            
            if ($request->page) {
                $payload['page'] = $request->page;
            }

            $response = Http::timeout(60)->withHeaders(['Origin' => $request->headers->get('origin')])->post($api, $payload);
            $responseData = $response->json();
            logApiRequestResponse(
                $api,
                'POST',
                $payload,
                $responseData,
                $response->status(),
                $response->headers(),
                'au-list-documents'
            );
            if ($response->successful() && isset($responseData['status']) && $responseData['status'] === true) {
                $data = $responseData['records']['data'] ?? [];
                $page = (int) request('page', 1);
                $perPage = (int) request('per_page', 10);
                $total = $responseData['records']['total'];

                $pagedData = array_slice($data, ($page - 1) * $perPage, $perPage);

                $start = ($page - 1) * $perPage ;
                $data = collect($data)->map(function ($item, $index) use ($start) {
                    $item['sr_no'] = $start + $index + 1;
                    $actionBy = User::find($item['action_by']);
                    $item['action_by_name'] = $actionBy ? trim(credential_decrypt($actionBy->name).' '.credential_decrypt($actionBy->middle_name).' '.credential_decrypt($actionBy->last_name)).' ('.$actionBy->employee_code.')' : 'N/A';

                    if (!empty($item['documents'])){
                            foreach ($item['documents'] as &$doc) {
                                
                                $parsedUrl = parse_url($doc['link']);
        
                                if (!empty($parsedUrl[ 'path' ]) && config('s3_download_link') == true) {
                                    $fileKey = ltrim($parsedUrl[ 'path' ], '/');
            
                                    $doc['link'] = Storage::disk('s3')->temporaryUrl(
                                        $fileKey,
                                        now()->addDays(7)
                                    );
                                }
                        
                            }
                        }
                        return $item;
                })->toArray();

                $paginator = new LengthAwarePaginator(
                    $pagedData,
                    $total,
                    $perPage,
                    $page,
                    ['path' => request()->url(), 'query' => request()->query()]
                );

                // EXCEL EXPORT
                if ($request->excelExport === true || $request->excelExport === 'true') {

                    $exportPayload = $payload;
                    $exportPayload['per_page'] = $total; 
                    
                    $exportResponse = Http::timeout(120)
                        ->withHeaders(['Origin' => $request->headers->get('origin')])
                        ->post($api, $exportPayload);
                    
                    $exportResponseData = $exportResponse->json();
                    
                    if (!$exportResponse->successful() || !isset($exportResponseData['status']) || $exportResponseData['status'] !== true
                    ) {
                        return response()->json([
                            'status' => false,
                            'message' => 'Failed to fetch full data for export',
                        ], 400);
                    }
                    
                    $data = $exportResponseData['records']['data'] ?? [];


                    $fileName = 'AU_Documents_' . now()->format('Ymd_His') . '.csv';
                    if(config('dashboard_storage_disk') === 's3'){
                       
                        $handle = fopen('php://temp', 'w+');


                        $filePath = Storage::disk('s3')->temporaryUrl($fileName, now()->addMinutes(30));
                    }else{
                        $filePath = Storage::url($fileName);

                        if (!file_exists(dirname($filePath))) {
                            mkdir(dirname($filePath), 0755, true);
                        }
    
                        $handle = fopen($filePath, 'w');                
    
                    }
                
                    // Columns
                    $columns = [
                        'SR No.',
                        'Trace Id.',
                        'CIF',
                        'RC NO',
                        'SP/RM Name',
                        'Name as per CIF',
                        'Mobile',
                        'Name as per RC',
                        'Approved By',
                        'Document Name',
                        'Doc Type',
                        'Uploaded On',
                        'Updated On',
                        'Status',
                        'Reason'
                    ];

                    fputcsv($handle, $columns);
                    
                    $srNo = 1;
                    
                    foreach ($data as $row) {

                        $actionBy = User::find($row['action_by']);
                    
                        $commonData = [
                            $row['customer_details']['reference_number'] ?? '',
                            $row['trace_id'] ?? '',
                            $row['vehicle_details']['vehicle_registration_no'] ?? '',
                            $row['customer_details']['customer_details']['spDetails']['agent_name'] ?? $row['agent_details']['agent_name'],
                            $row['customer_details']['customer_details']['fullName'] ?? '',
                            $row['customer_details']['customer_details']['mobileNumber'] ?? '',
                            $row['customer_details']['name_as_per_rc'] ?? '',
                            $actionBy ? trim(credential_decrypt($actionBy->name).' '.credential_decrypt($actionBy->middle_name).' '.credential_decrypt($actionBy->last_name)) : ''
                        ];
                    
                        // If documents exist → one row per document
                        if (!empty($row['documents'])) {
                            foreach ($row['documents'] as $doc) {
                    
                                fputcsv($handle, array_merge(
                                    [$srNo++],
                                    $commonData,
                                    [
                                        ucfirst($doc['doc_type'] ?? ''),
                                        $doc['doc_type'] ?? '',
                                        !empty($doc['created_at'])
                                            ? \Carbon\Carbon::parse($doc['created_at'])->format('d M Y H:i:s')
                                            : '',
                                        !empty($doc['updated_at'])
                                            ? \Carbon\Carbon::parse($doc['updated_at'])->format('d M Y H:i:s')
                                            : '',        
                                        strtoupper($doc['status'] ?? ''),
                                        $doc['reason'] ?? 'N/A',
                                    ]
                                ));
                            }
                        } else {
                            // No documents fallback
                            fputcsv($handle, array_merge(
                                [$srNo++],
                                $commonData,
                                ['', '', '', '', '', '']
                            ));
                        }
                    }

                if(config('dashboard_storage_disk') === 's3'){
                        rewind($handle);

                    $uploaded = Storage::disk('s3')->writeStream(
                        $filePath,
                        $handle
                    );
                    
                    if (is_resource($handle)) {
                        fclose($handle);
                    }
                    
                    if (!$uploaded) {
                        throw new \Exception('S3 upload failed');
                    }
                                
                    if (!Storage::disk('s3')->exists($filePath)) {
                        throw new \Exception('File not found in S3 after upload');
                    }
                 
                    $downloadUrl = Storage::disk('s3')->temporaryUrl(
                        $filePath,
                        now()->addMinutes(30)
                    );
                }else{
                    fclose($handle);
                    $downloadUrl = Storage::disk('public')->url("exports/{$fileName}");
                }
                    
                
                    return response()->json([
                        'status' => true,
                        'message' => 'File exported successfully',
                        'download_url' => $downloadUrl,
                    ]);
                }

                return response()->json([
                    'status' => true,
                    'data' => $data,
                    'pagination' => [
                        'current_page' => $paginator->currentPage()>$paginator->lastPage()? $paginator->lastPage():$paginator->currentPage(),
                        'per_page' => $paginator->perPage(),
                        'total' => $paginator->total(),
                        'last_page' => $paginator->lastPage(),
                        'next_page_url' => $paginator->nextPageUrl(),
                        'prev_page_url' => $paginator->previousPageUrl(),
                    ],
                ]);

            }

            return response()->json([
                'status' => false,
                'message' => 'API request failed',
            ], $response->status());

        } catch (Exception $e) {
            logApiRequestResponse(
                'listDocuments',
                'POST',
                $request->all(),
                ['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()],
                200,
                '',
                'au-list-documents'
            );
            Log::error('API error in listDocuments: '.$e->getMessage());

            return response()->json([
                'status' => false,
                'message' => 'Error connecting to API',
                'error' => $e->getMessage(),
            ], 400);
        }
    }

    public function UpdateDocuments(Request $request)
    {
        try {
            $api = credential_decrypt(config('updateDocuments.api'));
            if (empty($api)) {
                return response()->json([
                    'status' => false,
                    'message' => 'API URL not configured.',
                ], 400);
            }
            $user = Auth::user();
            $rules = [
                'enquiryId' => 'required',
                'id' => 'required',
                'status' => 'required|in:approved,rejected',
                'remarks' => 'required_if:status,rejected',
            ];
            $validator = Validator::make(request()->all(), $rules);
            if ($validator->fails()) {
                logApiRequestResponse(
                    'UpdateDocuments',
                    'POST',
                    $request->all(),
                    ['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()],
                    400,
                    '',
                    'au-update-documents'
                );

                return response()->json([
                    'status' => false,
                    'message' => 'Validation failed.',
                    'errors' => $validator->errors(),
                ], 422);
            }
            $payload = [
                'enqId' => $request->enquiryId,
                'id' => $request->id,
                'status' => $request->status,
                'remarks' => $request->remarks,
                'userID' => $user->id,
            ];

            $response = Http::timeout(60)->withHeaders(['Origin' => $request->headers->get('origin')])->post($api, $payload);
            logApiRequestResponse(
                $api,
                'POST',
                $payload,
                $response->json(),
                $response->status(),
                $response->headers(),
                'au-update-documents'
            );
            $response = Http::timeout(60)->withHeaders(['Origin' => $request->headers->get('origin')])->post($api, $payload);
            if ($response->successful()) {

                return response()->json([
                    'status' => true,
                    'data' => $response->json(),
                ]);

            }

            return response()->json([
                'status' => false,
                'message' => 'API request failed',
            ], $response->status());

        } catch (Exception $e) {
            logApiRequestResponse(
                'UpdateDocuments',
                'POST',
                $request->all(),
                ['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()],
                200,
                '',
                'au-update-documents'
            );
            Log::error('API error in updateDocuments: '.$e->getMessage());

            return response()->json([
                'status' => false,
                'message' => 'Error connecting to API',
                'error' => $e->getMessage(),
            ], 400);
        }
    }

    public function AuBranch(Request $request)
    {
        $page = $request->input('page', 1);
        $per_page = $request->input('per_page', 10);
        $dataQuery = AuBranch::query();
        if ($request->filled('search')) {
            $search = $request->search;
            $dataQuery->where(function ($query) use ($search) {
                $query->where('au_branch_dump.BranchName', 'like', "%{$search}%")
                    ->orWhere('au_branch_dump.BranchCode', 'like', "%{$search}%")
                    ->orWhere('au_branch_dump.BranchID', 'like', "%{$search}%");
            });
        }
        $data = $dataQuery->paginate($per_page);
        $lastPage = $data->lastPage();
        $prevPage = $page > 1 ? $page - 1 : null;
        $nextPage = $page < $lastPage ? $page + 1 : null;
        $startingNo = ($page - 1) * $per_page + 1;
        foreach ($data as $index => $item) {
            $item->srNo = $startingNo + $index;
        }

        return response()->json([
            'data' => $data->items(),
            'paginate' => [
                'per_page' => $data->perPage(),
                'current_page' => $page,
                'total' => $data->total(),
                'last_page' => $data->lastPage(),
                'next_page' => $nextPage,
                'prev_page' => $prevPage,
            ],
        ]);
    }

    public function Auhierarchy(Request $request)
    {
        $page = $request->input('page', 1);
        $per_page = $request->input('per_page', 10);
        $dataQuery = AUHierarchyDump::query();
        if ($request->filled('search')) {
            $search = $request->search;
            $dataQuery->where(function ($query) use ($search) {
                $query->where('au_hierarchy_dump.designation', 'like', "%{$search}%")
                    ->orWhere('au_hierarchy_dump.department_code', 'like', "%{$search}%")
                    ->orWhere('au_hierarchy_dump.department_name', 'like', "%{$search}%")
                    ->orWhere('au_hierarchy_dump.vertical_code', 'like', "%{$search}%");
            });
        }
        $data = $dataQuery->paginate($per_page);
        $lastPage = $data->lastPage();
        $prevPage = $page > 1 ? $page - 1 : null;
        $nextPage = $page < $lastPage ? $page + 1 : null;
        $startingNo = ($page - 1) * $per_page + 1;
        foreach ($data as $index => $item) {
            $item->srNo = $startingNo + $index;
        }

        return response()->json([
            'data' => $data->items(),
            'paginate' => [
                'per_page' => $data->perPage(),
                'current_page' => $page,
                'total' => $data->total(),
                'last_page' => $data->lastPage(),
                'next_page' => $nextPage,
                'prev_page' => $prevPage,
            ],
        ]);
    }

    public function importAUHierarchy(Request $request)
    {
        $request->validate([
            'file' => 'required|mimes:xlsx,xls,csv',
        ]);

        Excel::import(new HierarchyAUImport, $request->file('file'));

        return response()->json(['message' => 'Data imported successfully']);
    }

    public function importAUBranch(Request $request)
    {
        $request->validate([
            'file' => 'required|mimes:xlsx,xls,csv',
        ]);

        ini_set('memory_limit', '2048M');
        set_time_limit(0);

        Excel::import(new AUBranchImport, $request->file('file'));

        return response()->json(['message' => 'Data imported successfully']);
    }

    public function markUserActiveInactive(Request $request)
    {
        $request->validate([
            'user_id' => 'required|integer|exists:users,id',
            'counter' => 'required|integer', // if 0 then reset counter, if 1 then increase counter, if 3 then deactivate user
            // 3 for motor, 0,1 for dashboard
        ]);

        $user = User::where('id', $request->user_id)
            ->where('status', 'Y')
            ->first();

        if (! $user) {
            return response()->json(['message' => 'Invalid or inactive user'], 404);
        }

        DB::beginTransaction();

        try {

            // if($request->counter==3){
            //     $user->update(['status' => 'N']);
            //     DB::commit();
            //     return response()->json(['message' => 'User deactivated successfully'], 200);
            // }

            if ($request->counter == 0) {
                UserDeactivateCounter::where('user_id', $request->user_id)->delete();
                DB::commit();

                return response()->json(['message' => 'User activity reset successfully'], 200);
            }

            UserDeactivateCounter::create([
                'user_id' => $user->id,
                'deactivate_counter' => 1,
                'deactivate_status' => 'N',
                'created_at' => now(),
            ]);

            $userDeactiveCount = UserDeactivateCounter::where('user_id', $user->id)->count();

            if (config('Deactivate.User.On.Inactivity') && $userDeactiveCount >= 3) {
                // $user->update(['status' => 'N']);
                // DB::commit();
                return response()->json(['message' => 'User deactivated successfully'], 200);
            }

            DB::commit();

            return response()->json(['message' => 'User inactivity counter updated successfully'], 200);
        } catch (\Throwable $e) {
            DB::rollBack();

            return response()->json(['message' => 'Something went wrong', 'error' => $e->getMessage()], 400);
        }
    }

    public function userListingDeactivated(Request $request)
    {
        $user = Auth::user();
        if ($inactiveResponse = checkUserActivity($request)) {
            return $inactiveResponse;
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
            'users.qualification', 'users.profile_image',
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
                    ->orWhere('users.last_name', 'like', "%{$search}%");
            });
        }

        $userDeactiveCount = UserDeactivateCounter::where('user_id', $user->id)->count();

        if ($request->filled('user_status')) {
            $usersQuery->where('users.status', $request->user_status);
        }

        $perPage = $request->input('show', 10);
        $users = $request->input('paginate') === 'true'
            ? $usersQuery->paginate($perPage)
            : $usersQuery->get();

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

            $assignSupervisor = ($UpdatedPospRoleConfig == 'Y' && $userItem->usertype == 2);
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
                'employeeCode' => $userItem->usertype == 1 ? $userItem->employee_code : null,
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
                'parent_name' => $reportingTo ? credential_decrypt($reportingTo->name) : null,
                'reportingRole' => $reportingRole,
                'reportingTo' => $reportingTo ? [
                    'id' => $reportingTo->id,
                    'name' => credential_decrypt($reportingTo->name),
                ] : null,
                'reporting_Employee_Role' => $userItem->usertype == 1
                    ? $reportingRole
                    : ($reportingToRoleEmployee ? $reportingToRoleEmployee : null),
                'reporting_Employee' => $userItem->usertype == 1
                    ? ($reportingTo ? [
                        'id' => $reportingTo->id,
                        'name' => credential_decrypt($reportingTo->name),
                    ] : null)
                    : ($reportingToEmployee ? ['id' => $reportingToEmployee->id, 'name' => credential_decrypt($reportingToEmployee->name)] : null),
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
            'LastPage' => $request->input('paginate') ? $users->lastPage() : '',
            'total' => $request->input('paginate') ? $users->total() : '',
        ]);
    }

    public function activateUser(Request $request)
    {
        $auth = Auth::user();

        $validator = Validator::make($request->all(), [
            'user_id' => 'required|string',
        ]);

        if ($validator->fails()) {
            logApiRequestResponse(
                'activateUser',
                'POST',
                $request->all(),
                ['status' => 400, 'message' => 'Input Validation error', 'error' => $validator->errors()],
                400,
                '',
                'au-activate-user'
            );

            return response()->json([
                'status' => false,
                'message' => 'Validation Error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        $user = User::where('id', credential_decrypt($request->user_id))
            ->where('status', 'N')
            ->first();
        if ($user) {

            $user->status = 'Y';
            $user->update();

            $userDeactiveCount = UserDeactivateCounter::where('user_id', $request->user_id)->pluck('id')->toArray();

            UserActivateLog::insert([
                'activated_user_id' => credential_decrypt($request->user_id),
                'activated_by' => $auth->id,
                'recorded_ids' => implode(',', $userDeactiveCount),
                'created_at' => now(),
            ]);

            UserDeactivateCounter::where('user_id', $request->user_id)->delete();
            logApiRequestResponse(
                'activateUser',
                'POST',
                $request->all(),
                ['status' => 200, 'message' => 'User activated successfully', 'data' => [
                    'userId' => $user->id,
                ]],
                200,
                '',
                'au-activate-user'
            );

            return response()->json(['message' => 'User activated successfully'], 200);
        } else {
            return response()->json(['message' => 'Invalid or active user'], 404);
        }

    }

    public function importAllUserData(Request $request)
    {
        set_time_limit(0);
        ini_set('memory_limit','-1');
        
        $lobIds = lobMaster::where('is_enabled','Y')->pluck('id')->toArray();
    
        DB::table('au_user_dump')
            ->leftJoin('au_user_sp_dump', 'au_user_dump.SP_Codes', '=', 'au_user_sp_dump.SP_Codes')
            ->select('au_user_dump.*', 'au_user_sp_dump.BRANCH_NAME', 'au_user_sp_dump.Valid_From', 'au_user_sp_dump.Valid_Till', 'au_user_sp_dump.EMP_DOB', 'au_user_sp_dump.Insurance_Type')
            ->where('IsActive', 0)
            ->orderBy('id')
            ->chunk(500, function ($users) use ($request,$lobIds) {
            DB::beginTransaction();

            try {

                foreach ($users as $row) {

                    $reportingEmployeeCode = $row->UserLoginID;
                    // ===== USER TYPE LOGIC =====
                    if ($row->Sellertype == 'P') {
                        $userType = 3;
                    } elseif ($row->SP_Codes != '#N/A') {
                        $userType = 7;
                    } else {
                        $userType = 1;
                    }

                    // ===== REPORTING TO (cached) =====
                    if($row->ReportingTo!='0' && $row->ReportingTo!=''){
                        $reportingToData = User::where('username', credential_encrypt($row->ReportingTo))->first();
                        if(! $reportingToData){                
                            $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                        }
                        if ($row->Sellertype == 'P') {
                            if ($reportingToData->usertype == 3) {
                                $reportingTo = $reportingToData->id;
                            } else {
                                $reportingEmployeeCode = $row->ReportingTo;
                                $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                            }
                        } else {
                            if ($reportingToData) {
                                $reportingTo = $reportingToData->id;
                            } else {
                                $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                            }
                        }
                    }else{
                        $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                    }

                    $qrCode_generated = generateQrcode();
                    $secret = $qrCode_generated['secret'];
                    $totp_secret = credential_encrypt($secret);

                    $password = 'Admin@123';

                    // ===== NAME CLEAN =====
                    $name = preg_replace('/\b(mr|mrs|ms|miss|dr)\.?\s*/i', '', $row->UserName);
                    $name = trim(preg_replace('/\s+/', ' ', $name));
                    $name = ucwords(strtolower($name));

                    $parts = array_values(array_filter(explode(' ', trim($name))));

                    $firstName = $parts[0] ?? '';
                    $lastName  = count($parts) > 1 ? array_pop($parts) : '';
                    $middleName = implode(' ', array_slice($parts,1));

                    $fullName = trim($firstName . ' ' . $middleName . ' ' . $lastName);

                    preg_match('/\b\d{6}\b/', $row->Address, $matches);

                    $pincode = $matches[0] ?? null;

                    // ===== UPSERT USER =====
                    $inserted = User::updateOrCreate(
                        ['username' => credential_encrypt($row->UserLoginID)], 
                        ['name' => credential_encrypt($firstName),
                        'middle_name' => credential_encrypt($middleName),
                        'last_name' => credential_encrypt($lastName),
                        'email' => credential_encrypt($row->EmailID),
                        'mobile' => credential_encrypt($row->MobileNo),
                        'gender' => ($row->Gender),
                        'address' => credential_encrypt($row->Address),
                        'pincode' => credential_encrypt($pincode),
                        'password' => Hash::make($password),
                        'totp_secret' => $totp_secret,
                        'employee_code' => $reportingEmployeeCode,
                        'status' => 'Y',
                        'usertype' => $userType,
                        'zone_id' => 1,
                        'reportingto' => $reportingTo,
                        'pan_no' => credential_encrypt($row->PanNo),
                        'dob' => $row->EMP_DOB ? credential_encrypt($row->EMP_DOB) : null,
                        'user_code' => $row->UserLoginID,
                    ]);
    
                        // ===== ADDITIONAL DATA =====


                    $user_id = $inserted->id;
                    // $date_of_joining = $request->filled('DateOfJoining') ? Carbon::parse($request->DateOfJoining)->endOfDay() : null;
                    // $date_of_leaving = $request->filled('DateOfLeaving') ? Carbon::parse(trim($request->DateOfLeaving))->endOfDay() : null;
                    $certificate_valid_from = $row->Valid_From ? Carbon::parse(trim($row->Valid_From))->startOfDay() : null;
                    $certificate_valid_till = $row->Valid_Till ? Carbon::parse(trim($row->Valid_Till))->endOfDay() : null;

                    $user_role_id = AUHierarchyDump::where('designation', $row->functionalRole)->first()->role_id ?? null;
                    $user_role_id = $user_role_id ?? ($row->SP_Codes != '#N/A' ? 12 : ($row->Sellertype === 'P' ? 7 : 13));
                    $user_role_id = $row->SP_Codes != '#N/A' ? 12 : $user_role_id;

                    $inserted = UserAdditionalData::updateOrCreate(
                        ['user_id' => $user_id,],[
                        'job_id' => $row->JobID,
                        // 'date_of_joining' => $date_of_joining,
                        // 'date_of_leaving' => $date_of_leaving,
                        'role_id' => $user_role_id,
                        'RBM' => $row->RBM,
                        'CBM' => $row->CBM,
                        'department_code' => $row->DepartmentCode,
                        'vertical_code' => $row->VerticalID,
                        'functional_role' => $row->functionalRole,
                        'user_salary' => $row->UserSalary,
                        'is_sp' => $row->SP_Codes != '#N/A' ? 'Y' : 'N',
                        'sp_name' => $fullName,
                        'sp_code' => $row->SP_Codes,
                        'sp_type' => $row->Insurance_Type,
                        'certificate_valid_from' => $certificate_valid_from,
                        'certificate_valid_till' => $certificate_valid_till,
                    ]);
        
                    $branch_id = DB::table('au_branch_dump')->where('BranchCode', $row->BranchCode)->pluck('BranchID');

                    foreach ($branch_id as $branch_value) {
                        DB::table('user_branch_relation')
                            ->where('user_id', $user_id)->where('branch_id', $branch_value)
                            ->delete();

                        $inserted = DB::table('user_branch_relation')->insert([
                            'user_id' => $user_id,
                            'branch_id' => $branch_value,
                        ]);
                    }

                    $request->merge(['user_id' => $user_id, 'role_id' => $user_role_id]);

                    $userrolemapping = $this->userRoleMapping->UserRoleMapping($request);

                    SellNow::where('user_id', $user_id)->delete();

                    foreach ($lobIds as $value) {

                        $userlobMapping = SellNow::create([
                            'user_id' => $user_id,
                            'lob_id' => $value,
                            'created_at' => Carbon::now(),
                            'updated_at' => null,
                        ]);
                    }

                    DB::table('au_user_dump')->where('id', $row->id)->update(['IsActive'=>1]);
    
                    DB::commit();
                }
    
            } catch (\Throwable $e) {
                DB::rollBack();
                throw $e;
            }
        });
    
        return response()->json([
            'status' => 200,
            'message' => '61K users imported successfully'
        ]);
    }
    
}
