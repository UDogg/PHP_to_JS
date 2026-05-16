<?php

namespace App\Http\Controllers\User;

use App\Events\requestQrEvent;
use App\Exports\UserDataExport;
use App\Http\Controllers\Controller;
use App\Http\Controllers\RolesController;
use App\Http\Controllers\SellNowController;
use App\Http\Requests\UserBankDetailsReq;
use App\Imports\UpdateUserMappingOneClick;
use App\Jobs\ExportLargeExcel;
use App\Mail\GoogleAuthenticationEmail;
use App\Models\Broker;
use App\Models\Customer;
use App\Models\EmailActivityLog;
use App\Models\ExcelDownloadLog;
use App\Models\ifscCodeMaster;
use App\Models\lobMaster;
use App\Models\QualificationMaster;
use App\Models\SellNow;
use App\Models\TemplateModel;
use App\Models\User;
use App\Models\UserMapping;
use App\Models\userTypes;
use App\Models\ZoneMasterModel;
use App\Services\UserService;
use Carbon\Carbon;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Database\QueryException;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Mail;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use Maatwebsite\Excel\Facades\Excel;
use Spatie\Permission\Models\Permission;
use Spatie\Permission\Models\Role;
use App\Models\VisibilityReportDownloadReport;

class UserController extends Controller
{
    protected $userRoleMapping;

    protected $userData;

    protected $userService;

    public function __construct(Auth $auth, RolesController $rolecontroller, SellNowController $sellNowController, UserService $userService)
    {
        $this->userData = $auth::user();
        $this->userRoleMapping = $rolecontroller;
        $this->UserlobMapping = $sellNowController;
        $this->userService = $userService;
    }

    public function index(Request $request)
    {
        $permission = credential_decrypt(config('Permission.user.view'));
        if (! $this->userData->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }

        $users = User::withTrashed()->select('users.id', 'users.name', 'users.username', 'users.email', 'users.mobile', 'users.gender', 'users.address', 'users.pincode', 'users.status', 'users.usertype', 'roles.name as role_name', 'parent.name as reportingrolename','users.adhar_no','users.pan_no')->leftJoin('users as parent', 'users.reportingto', '=', 'parent.id')->leftJoin('model_has_roles', 'model_has_roles.model_id', '=', 'users.id')->leftJoin('roles', 'model_has_roles.role_id', '=', 'roles.id');
        $columns = $users;
        $user_count = $users->get();
        $users = $users->orderBy('id', 'desc')->paginate(10);
        if (count($user_count) != 0) {
            $columns = $users;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['id', 'username', 'name', 'email', 'mobile', 'gender', 'address', 'pincode', 'status', 'Usertype','adhar_no','pan_no'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'id') {
                $columns[$key] = 'Id';
            } elseif ($value === 'username') {
                $columns[$key] = 'User Name';
            } elseif ($value === 'name') {
                $columns[$key] = 'Name';
            } elseif ($value === 'email') {
                $columns[$key] = 'Email';
            } elseif ($value === 'mobile') {
                $columns[$key] = 'Mobile';
            } elseif ($value === 'gender') {
                $columns[$key] = 'Gender';
            } elseif ($value === 'address') {
                $columns[$key] = 'Address';
            } elseif ($value === 'pincode') {
                $columns[$key] = 'Pincode';
            } elseif ($value === 'status') {
                $columns[$key] = 'Status';
            } elseif ($value === 'rolename') {
                $columns[$key] = 'Role Name';
            } elseif ($value === 'reportingrolename') {
                $columns[$key] = 'Reporting Role Name';
            } elseif ($value === 'adhar_no') {
                $columns[$key] = 'Adhar';
            } elseif ($value === 'pan_no') {
                $columns[$key] = 'Pan';
            } else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }

        if ($request->has('search') && ! empty($request->search)) {

            $search = credential_encrypt($request->search);
            $query = User::query();

            $query->where('id',  $request->search)
                  ->orWhere('name', 'LIKE', "%{$search}%")
                ->orWhere('email', 'LIKE', "%{$search}%")
                ->orWhere('mobile', 'LIKE', "%{$search}%")
                ->orWhere('username', 'LIKE', "%{$search}%");

            $users = $query->paginate(10);
        }

        return view('user.index', compact('users', 'columns'));
    }

    public function UserBankDetails(UserBankDetailsReq $request, int $id)
    {
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->userData->can($permission)) {

            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $user = User::find($id);
        $user->bank_name = credential_encrypt($request->bank_name);
        $user->bank_city = credential_encrypt($request->bank_city);
        $user->account_no = credential_encrypt($request->account_no);
        $user->ifsc_code = credential_encrypt($request->ifsc_code);
        $user->bank_branch = credential_encrypt($request->branch);
        $user->account_holder_name = credential_encrypt($request->account_holder_name);
        //    genenrate json request with dummy data for testing in postman
        $user->save();
        $userId = $user->id;
        if ($user) {

            return requestResponseMessage(['status' => 200, 'message' => 'User Updated Successfully', 'data' => [
                'email' => $request->email,
                'userId' => $userId,
            ]]);

        } else {
            return requestResponseMessage(['status' => 404, 'message' => 'Error While Updating User.']);
        }

    }

    private function DefaultDashboardAccess(): array
    {
        $user = Auth::user();
        $permission = Permission::select('name')->where('name', 'Dashboard.view')->first();
        $role = $user->getRoleNames();
        $role->givePermissionTo($permission->name);

        return [
            'status' => 200,
        ];
    }

    private function UserMapUsertype($userId, $usertype, $role_id, $reportingTo)
    {
        $checkInMappings = UserMapping::where('user_id', $userId)->where('user_type', $usertype)->first();
        if ($checkInMappings) {
            return requestResponseMessage(['status' => 500, 'message' => 'User  Already Exists please Try with other email username and mobile number']);
        }
        $PresentUserId = $userId;
        UserMapping::insert([
            'user_id' => $PresentUserId,
            'user_type' => $usertype,
            'role_id' => $role_id,
            'reportingto' => $reportingTo,
            'created_at' => Carbon::now(),
        ]);

    }

    public function store(Request $request)
    {
        $authenticatedUser = Auth::user();

        $employe_code_of_current_user = $authenticatedUser->employee_code;
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->userData->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $AllowMultipleUsers = config('Broker.Allow.Multiple.users');
        $defaultPartnerUserForPosp = config('Broker.Default.Partner');

        $rules = [
            'username' => 'required|string',
            'name' => 'required|string',
            // 'middle_name' => 'required|string',
            // 'last_name' => 'required|string',
            'mobile' => 'required|regex:/^[0-9]{10}$/',
            'email' => 'required|email',
            'gender' => 'required|string|in:M,F',
            'address' => 'required|string',
            'pincode' => 'required|digits:6',
            'status' => 'required|in:N,Y',
            // 'user_type' => 'required|integer',
            // 'role_id' => 'required|integer',
            // 'lob_id' => 'required|array',
            // 'qualification' => 'required|integer',
            // 'dob' => 'required|date_format:d/m/Y',
        ];

        $getusertype = userTypes::select('name', 'Identifier')->where('id', $request->getusertype)->where('is_active', 'Y')->first();
        if ($getusertype->Identifier == 'MISP') {
            $rules['oemId'] = 'required|integer';
            $rules['mispId'] = 'required|integer';
            $rules['branchId'] = 'required|integer';
        }
        $userCode = '';
        $reportingEmployeeCode = null;
        if ($getusertype->Identifier == 'E') {
            $validate = $request->validate([
                'employeeCode' => 'required|string',
            ]);
            if (User::where('employee_code', $request->employeeCode)->exists()) {
                return response()->json(['message' => 'The employee code already exists.'], 422);
            }
            $reportingEmployeeCode = $request->employeeCode;
        }
        if ($getusertype->Identifier == 'P') {
            $validate = $request->validate([
                'posCode' => 'required|string',
                'license_start_date' => 'required|date_format:d/m/Y',
                'license_end_date' => 'required|date_format:d/m/Y',
            ]);
            $userCode = $request->posCode;

            $reportingEmployeeCode = User::select('employee_code')->where('id', $request->reportingEmployee)->first()['employee_code'] ?? 0;

        }
        if ($getusertype->Identifier == 'Partner') {
            $reportingEmployeeCode = $employe_code_of_current_user ?? 0;

        }
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return requestResponseMessage(['status' => 500, 'message' => 'Input Validation error', 'error' => $validator->errors()]);
        }

        $check_mail = User::select('email', 'id')->where('email', credential_encrypt($request->email))->orWhere('username', credential_encrypt($request->username))->orWhere('mobile', credential_encrypt($request->mobile))->first();
        if ($check_mail) {
            if ($AllowMultipleUsers == 'Y' || ($defaultPartnerUserForPosp == 'Y' && $getusertype->Identifier == 'P')) {
                $this->UserMapUsertype($check_mail->id, $request->user_type, $request->role_id, $request->reportingTo);

                return response()->json([
                    'status' => 200,
                    'message' => 'User Created Successfully',
                ]);
            } else {
                return requestResponseMessage(['status' => 500, 'message' => 'User  Already Exists please Try with other email username and mobile number']);
            }
        } else {
            try {
                $qrCode_generated = generateQrcode();
                $secret = $qrCode_generated['secret'];
                $totp_secret = credential_encrypt($secret);
                
                $password = generateRandomPassword(8);
                
                $inserted = User::updateOrCreate([
                    'username' => credential_encrypt($request->username) ?? null,
                    'name' => credential_encrypt($request->name) ?? null,
                    'middle_name' => credential_encrypt($request->middle_name) ?? null,
                    'last_name' => credential_encrypt($request->last_name) ?? null,
                    'email' => credential_encrypt($request->email),
                    'mobile' => credential_encrypt($request->mobile),
                    'gender' => ($request->gender),
                    'address' => credential_encrypt($request->address),
                    'pincode' => credential_encrypt($request->pincode),
                    'password' => Hash::make($password),
                    'totp_secret' => $totp_secret,
                    'employee_code' => $reportingEmployeeCode,
                    'status' => $request->status,
                    'usertype' => $request->getusertype,
                    'zone_id' => $request->zoneId,
                    'reportingto' => $request->reportingTo,
                    'pan_no' => credential_encrypt($request->pan_no),
                    'adhar_no' => credential_encrypt($request->adhar_no),
                    'qualification' => $request->qualification,
                    'dob' => credential_encrypt($request->dob) ?? null,
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
                    $request->merge(['user_id' => $user_id]);
                    // $userDashboardAccess = $this->DefaultDashboardAccess();
                    // dd($request);
                    $userrolemapping = $this->userRoleMapping->UserRoleMapping($request);

                    $lobIds = $request->lob_id;
                    foreach ($request->lob_id as $value) {

                        $userlobMapping = SellNow::create([
                            'user_id' => $user_id,
                            'lob_id' => $value,
                            'created_at' => Carbon::now(),
                            'updated_at' => Carbon::now(),
                        ]);
                    }
                    // if($defaultPartnerUserForPosp == 'Y' && $getusertype->Identifier == 'P')
                    // {
                    //     $partnerUsertypeId = userTypes::select('id')->where('Identifier', 'Partner')->first()['id'];
                    //     $this->UserMapUsertype($user_id,$partnerUsertypeId,$request->role_id,$request->reportingTo);
                    // }
                    // }
                    // if(!$userlobMapping)
                    // {
                    //     return response()->json([
                    //         'status' => 500,
                    //         'message' => 'Error While Mapping lob to User.',
                    //     ]);
                    // }
                    $new_email = $request->email;
                    $broker = Broker::first();
                    if ($broker && $broker->is_email === 'Y') {
                        // Fetch the appropriate email template
                        $contentData = TemplateModel::where('event', 'User Creation')->exists()
                        ? TemplateModel::where('event', 'User Creation')->get()
                        : TemplateModel::where('event', 'add_email_template')->get();

                        foreach ($contentData as $data) {
                            $title = $data->title ?? 'O T P Verification Mail';
                            $content = $data->content ?? 'Please Add Template Content From Template';
                            $decodedContent = html_entity_decode($content);

                            $plainTextTitle = strip_tags($decodedContent);
                            $body = $plainTextTitle ?: 'Default Body';

                            // Trigger the event
                            event(new requestQrEvent($new_email, $qrCode_generated['QrCode'], $secret, $password, $body, $title));

                            EmailActivityLog::create([
                                'email' => $new_email,
                                'subject' => 'QR Code Sent',
                                'body' => $body,
                                'type' => 'QR Code Sent',
                                'status' => 'Email Sent',
                                'sent_at' => now(),
                            ]);
                        }
                    }

                    return redirect()->route('user.index')->with('success', 'User Created Successfully');
                    // return requestResponseMessage(['status' => 200, 'message' => 'User Created Successfully', 'data' => [
                    //     'email' => $new_email,
                    //     'userId' => $user_id,
                    // ]]);

                } else {
                    return requestResponseMessage(['status' => 404, 'message' => 'Error While Creating User.']);
                }
            } catch (\Exception $e) {
                return requestResponseMessage(['status' => 404, 'message' => 'Something went wrong: '.$e->getMessage()]);
            }
        }
    }

    public function create()
    {
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->userData->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $getusertype = userTypes::select('id', 'name', 'Identifier')
            ->where('is_active', 'Y')
            ->get();
        $getLob = lobMaster::select('id', 'lob')
            ->where('is_enabled', 'Y')
            ->get();

        $getRole = Role::select('id', 'name')
            ->get();

        $qrCode = generateQrcode();

        return view('user.create', compact('qrCode', 'getusertype', 'getLob', 'getRole'));
    }

    public function edit(User $user)
    {
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->userData->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }

        $fieldsToDecrypt = [
            'username', 'name', 'email', 'mobile',
            'address', 'pincode', 'pan_no', 'adhar_no',
        ];

        $user = decryptUserData($user, $fieldsToDecrypt);
        $getusertype = userTypes::select('id', 'name', 'Identifier')
            ->where('is_active', 'Y')
            ->get();

        $getLobs = lobMaster::select('id', 'lob')
            ->where('is_enabled', 'Y')
            ->get();

        return view('user.edit', compact('user', 'getusertype', 'getLobs'));
    }

    public function update(Request $request)
    {
        $reportingEmployeeCode = null;
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->userData->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $getusertype = userTypes::select('name', 'Identifier')->where('id', $request->user_type)->where('is_active', 'Y')->first();
        $userCode = '';
        if ($getusertype->Identifier == 'E') {
            $validate = $request->validate([
                'employeeCode' => 'required|string',
            ]);

            $employeeExists = User::where('employee_code', $request->employeeCode)
                ->where('id', '!=', $request->id)
                ->exists();

            if ($employeeExists) {
                return response()->json(['message' => 'The employee code already exists for another user.'], 422);
            }

            $mobileExists = User::where('mobile', credential_encrypt($request->mobile))
                ->where('id', '!=', $request->id)
                ->exists();

            if ($mobileExists) {
                return response()->json(['message' => 'The mobile number already exists for another user.'], 422);
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
            ]);
            $userCode = $request->posCode;
            $reportingEmployeeCode = $this->getPosReportingEmployeeCode($request->reportingEmployee);
        }
        if ($getusertype->Identifier == 'Partner') {

            // $reportingEmployeeCode = $this->getPosReportingEmployeeCode($request->reportingTo);
            $reportingEmployeeCode = $request->employeeCode ?? 0;
        }
        $user = User::find($request->id);
        $qrCode_generated = generateQrcode();
        $secret = $qrCode_generated['secret'];
        $totp_secret = credential_encrypt($secret);
        //        $password = generateRandomPassword(8);
        $updated = $user->update([
            'username' => credential_encrypt($request->username),
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
            'reportingto' => $request->reportingTo,
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

        if ($request->has('sync_hierarchy') && $request->sync_hierarchy) {
            $empMobile = User::where('reportingto', $request->reportingTo)->pluck('mobile')->first();

            $client = new Client;
            $headers = ['Content-Type' => 'application/json'];
            $apiUrl = config('hierarchy_sync');
            $methodType = 'GET';
            $body = [
                'pos_mobile' => $request->mobile,
                'emp_mobile' => $empMobile,
            ];
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);
        }

        $userbankdetailsreq = new UserBankDetailsReq($request->all());
        $userbankdetails = $this->UserBankDetails($userbankdetailsreq, $request->id);
        $userlobmappings = SellNow::select('lob_id')->where('user_id', $request->id)->pluck('lob_id')->toArray();
        foreach ($request->lob_id as $lobuserval) {
            if (! in_array($lobuserval, $userlobmappings)) {
                $userlobmapping = SellNow::insert([
                    'user_id' => $request->id,
                    'lob_id' => $lobuserval,
                    'created_at' => Carbon::now(),
                ]);
            }
        }
        foreach ($userlobmappings as $ulmap) {
            if (! in_array($ulmap, $request->lob_id)) {
                SellNow::where('user_id', $request->id)->where('lob_id', $ulmap)->delete();
            }

        }
        if ($updated) {
            return requestResponseMessage(['status' => 200, 'message' => 'User Updated Successfully', 'data' => ['email' => $request->email]]);
        } else {

            return requestResponseMessage(['status' => 404, 'message' => 'Error While Updating User.']);

        }
    }

    public function editUserDoc($id)
    {
        $user = User::findOrFail($id);

        $fieldsToDecrypt = [
            'pan_no',
            'adhar_no',
        ];

        $user = decryptUserData($user, $fieldsToDecrypt);

        return view('user.edit_user_doc', compact('user'));
    }

    public function updateUserDoc(Request $request, $id)
    {
        $user = User::findOrFail($id);
        $request->validate([
            'pan_no'   => 'nullable|string|max:20',
            'adhar_no' => 'nullable|string|max:20',
            'status'   => 'required|in:Y,N',
        ]);

        $user->adhar_no = credential_encrypt($request->adhar_no);
        $user->pan_no   = credential_encrypt($request->pan_no);

        $user->status = $request->status;
        $user->save();

        return redirect()
            ->route('user.index')
            ->with('success', 'User updated successfully');
    }


    public function destroy(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $permission = credential_decrypt(config('Permission.UserCreation.edit'));
        if (! $this->userData->can($permission)) {
            return back()->with('error', 'Access Denied');
        }
        $id = $request->id ?? $request->user_id;
        if (! $this->userData->can('user.delete')) {
            return back()->with('error', 'Access Denied');
        }
        $user = User::find($id);
        if (! $user) {
            return back()->with('error', 'User not found.');
        }
        if ($user->delete()) {
            return redirect()->route('user.index')->with('success', 'User Deleted Successfully');
        } else {
            return back()->with('error', 'Error While Deleting the User.');
        }
    }

    public function restore($id)
    {
        $user = User::withTrashed()->find($id);

        if (! $user) {
            return response()->json(['status' => 404, 'message' => 'User not found.']);
        }

        $user->restore();

        return response()->json(['status' => 200, 'message' => 'User restored successfully.']);
    }

    public function showEmailIdForm()
    {
        return view('auth.askEmailForm');

    }

    public function resendQrCode(Request $request)
    {
        $validateData = [
            'requested_email' => 'required|email',
        ];

        $validator = Validator::make($request->all(), $validateData);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator)->withInput();
        } else {

            $contentData = TemplateModel::where('event', 'Send OTP')->exists()
            ? TemplateModel::where('event', 'Request QR')->get()
            : TemplateModel::where('event', 'add_email_template')->get();

            foreach ($contentData as $contentData) {
                $title = $contentData->title ?? 'O T P Verification Mail';
                $content = $contentData->content ?? 'Please Add Template Content From Template';
                $decodedContent = html_entity_decode($content);

                $plainTextTitle = strip_tags($decodedContent);
                $body = $plainTextTitle ?: 'Default Body';
                $new_email = $request->requested_email;
                $user = User::where('email', $new_email)->first();

                $qrCode_generated = generateQrcode();
                $qrcode = $qrCode_generated['QrCode'];
                $secret = $qrCode_generated['secret'];
                $password = $user->password;
                event(new requestQrEvent($new_email, $qrcode, $secret, $password, $body, $title));
                // Mail::to($new_email)->send(new GoogleAuthenticationEmail($qrcode,$qrCode_generated['secret'],$user->password));
                EmailActivityLog::create([
                    'email' => $new_email,
                    'subject' => 'QR Code Resent',
                    'body' => 'QR Code Resent.',
                    'type' => 'QR Code Resent',
                    'status' => 'Email Sent',
                    'sent_at' => now(),
                ]);
                User::where('email', $new_email)->update([
                    'totp_secret' => credential_encrypt($qrCode_generated['secret']),
                ]);
                Auth::logout();

                return redirect()->intended('/');
            }
        }
    }

    public function BankDetails(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $permission = credential_decrypt(config('Permission.user.view'));
        if (! $this->userData->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        if ($request->has('ifscCode') && ! empty($request->ifscCode)) {
            $validator = Validator::make($request->all(), [
                'ifscCode' => 'string|max:15|min:11',
            ]);
            if ($validator->fails()) {
                return response()->json(['message' => $validator->errors()->first()], 400);
            } else {
                $ifscCode = strtoupper($request->ifscCode);
                $bankDetails = collect(ifscCodeMaster::where('ifsc_code', $ifscCode)->first());
                $bankDetails = $bankDetails->except('bank_id')->all();
                if (empty($bankDetails)) {
                    return response()->json([
                        'status' => 404,
                        'message' => 'Bank Not Found',
                    ], 404);
                }

                return response()->json([
                    'status' => 200,
                    'bankDetails' => $bankDetails,
                ]);
            }
        }
        if (! empty($request->bank_name)) {
            $bankDetails = ifscCodeMaster::select('bank_name', 'ifsc_code', 'bank_branch', 'address', 'district', 'state', 'bank_city', 'std_code');
            if (! empty($request->bank_state)) {
                $bankDetails = $bankDetails->where('state', $request->bank_state);
            }
            if (! empty($request->bank_city)) {
                $bankDetails = $bankDetails->where('bank_city', $request->bank_city);
            }
            if (! empty($request->bank_branch)) {
                $bankDetails = $bankDetails->where('bank_branch', 'like', '%'.$request->bank_branch.'%');
            }
            $bankDetails = $bankDetails->where('bank_name', $request->bank_name)->get()->toArray();

            return response()->json([
                'status' => 200,
                'bankDetails' => $bankDetails,
            ]);
        } else {
            return response()->json([
                'status' => 404,
                'message' => 'Bank Not Found',
            ], 404);
        }

    }

    public function getUsersData(Request $request)
    {

        $rules = [
            'email' => 'nullable|email',
            'mobile_no' => 'required|digits:10',
        ];

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
        ];
        $methodType = 'POST';

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 422);
        }

        if ($request->filled(['mobile_no'])) {
            $email = $request->email ?? null;
            $mobileNo = credential_encrypt($request->mobile_no);

            $username = $request->mobile_no;
            $name = strstr($email, '@', true); // Get everything before '@'

            $existingUser = Customer::where('mobile', $mobileNo)->first();

            if ($existingUser) {

                return [
                    'status' => 'true',
                    'message' => 'User with this mobile no already exists',
                    'user_id' => $existingUser->id,
                    'remote_user_id' => '',
                ];
            }

            DB::beginTransaction();
            try {
                $user_type = userTypes::select('id')->where('Identifier', 'U')->first()['id'] ?? null;
                $role_id = DB::table('roles')
                    ->where('user_type', 5)
                    ->pluck('id')
                    ->first();
                $newUser = Customer::create([
                    'email' => credential_encrypt($email) ?? '',
                    'mobile' => $mobileNo,
                    // "name" => !empty($name) ? credential_encrypt($name) : credential_encrypt($username),
                    'password' => Hash::make('Pass@123'),
                    'username' => $mobileNo,
                    // "address" => "",
                    'role_id' => $role_id,
                    'usertype' => $user_type,
                ]);

                // GET USER ID
                $insertedId = $newUser->id;

                if (empty($role_id)) {
                    return requestResponseMessage(['status' => 403, 'message' => 'Role Not Found']);
                }

                // THEN ASSIGN PERMISSION OF CUSTOMER TO USE
                $CustomerAssignRole = DB::table('model_has_roles')->insert([
                    'role_id' => $role_id,
                    'model_type' => 'App\Models\Customer',
                    'model_id' => $insertedId,
                ]);
                // assignLobs($newUser->id);

                DB::commit(); // Commit if everything is fine

                return response()->json([
                    'status' => 'true',
                    'message' => 'User created successfully',
                    'user_id' => $newUser->id,
                    'remote_user_id' => '',
                ]);
            } catch (\Exception $e) {
                DB::rollBack();
                if (config('store_api_logs') == true) {
                    logApiRequestResponse(
                        $apiUrl ?? ' ',
                        $methodType,
                        $request->all(),
                        $e->getMessage() ?? null,
                        $e->getCode() ?? null,
                        $headers
                    );
                }

                return response()->json(['error' => $e->getMessage()], 500);

            }
        } else {
            return response()->json([
                'status' => 'false',
                'message' => 'Something went wrong',
                'user_id' => '',
                'remote_user_id' => '',
            ]);

        }
    }

    public function GetRoleHireachy(Request $request)
    {
        $user = Auth::user();
        $userTypeId = $user->usertype;
        $roles_id = $user->roles->pluck('id')[0];
        $reporting_roles = RoleHierarchy($roles_id, $userTypeId);

        return response()->json($reporting_roles);

    }

    protected function getPosReportingEmployeeCode($employeeId)
    {
        $EnsuringEmployeeUser = userTypes::select('id')->where('Identifier', 'E')->first()['id'];
        $reportingEmployeeCode = User::select('employee_code')->where('id', $employeeId)->where('usertype', $EnsuringEmployeeUser)->first()['employee_code'] ?? 0;

        return $reportingEmployeeCode;

    }

    public function PospUploadData(Request $request)
    {
        // $user = Auth::user();
        $employee_mobile_no = $request->rm_number;
        $employee_mobile_no_check = User::where('mobile', credential_encrypt($employee_mobile_no))->exists();
        $check_if_user_exists = User::where('mobile', credential_encrypt($request->mobile))->exists();
        $is_new_emp_created = 0;

        if ($check_if_user_exists) {
            return response()->json([
                'status' => 409,
                'message' => 'User Exist.',
            ], 409);
        } else {

            if ($employee_mobile_no_check) {
                // if employee exists do nothing
            } else {
                $emp_userType_id = userTypes::where('name', 'Employee')->pluck('id')->first();
                $emp = User::create([
                    'username' => credential_encrypt($request->rm_name),
                    'name' => credential_encrypt($request->rm_name),
                    'email' => credential_encrypt($request->rm_email),
                    'mobile' => credential_encrypt($request->rm_number),
                    'password' => bcrypt('Admin@1234'),
                    'usertype' => $emp_userType_id,
                    // 'reportingto' => $reporting_role->id,
                    'employee_code' => $request->rm_number,
                    'address' => credential_encrypt('Mumbai'),
                ]);

                $is_new_emp_created = 1;
            }

        }

        $emp_code = User::where('mobile', credential_encrypt($employee_mobile_no))->pluck('employee_code')->first();

        $password = generateRandomPassword(8);
        try {
            $user_type = userTypes::where('Identifier', 'P')->first();
            $reporting_role = DB::table('roles')->where('user_type', $user_type->id)->first();
            $qualification = QualificationMaster::where('qualification_name', 'like', '%'.$request->educational_qualification.'%')->first();
            $products = explode(', ', $request->products);
            $lob = lobMaster::whereIn('lob_master_name', $products)->get();
            $user = User::create([
                'username' => credential_encrypt($request->agent_name),
                'name' => credential_encrypt($request->user_name),
                'email' => credential_encrypt($request->email),
                'mobile' => credential_encrypt($request->mobile),
                'address' => credential_encrypt($request->address),
                'pan_no' => credential_encrypt($request->pan_no),
                'adhar_no' => credential_encrypt($request->aadhar_no),
                'dob' => credential_encrypt($request->date_of_birth),
                'gender' => ($request->gender === 'male') ? 'M' : (($request->gender === 'female') ? 'F' : null),
                'qualification' => $qualification->qualification_master_id,
                'bank_name' => credential_encrypt($request->bank_name),
                'bank_branch_name' => credential_encrypt($request->bank_branch),
                'bank_account_no' => credential_encrypt($request->account_no),
                'ifsc_code' => credential_encrypt($request->ifsc_code),
                'license_start_date' => $request->licence_start_date,
                'licence_end_date' => $request->licence_end_date,
                'password' => bcrypt('Admin@1234'),
                'usertype' => $user_type->id,
                'pincode' => $request->pincode,
                // 'reportingto' => $user->usertype,
                'employee_code' => $emp_code,
            ]);

            if ($user) { // this is done for pos
                $role_id = DB::table('roles')
                    ->where('name', 'Posp')
                    ->pluck('id')
                    ->first();

                $model_id = User::where('mobile', $user->mobile)->pluck('id')->first();

                DB::table('model_has_roles')->insert([
                    'role_id' => $role_id,
                    'model_type' => 'App\Models\User',
                    'model_id' => $model_id,
                ]);
            }

            if ($user) {  // for users_mapping [this is done for partner]
                $user_id = User::where('mobile', $user->mobile)->pluck('id')->first();
                $user_type_id = DB::table('usertypes')
                    ->where('name', 'Partner')
                    ->pluck('id')
                    ->first();

                $users_mapping = UserMapping::create([
                    'user_id' => $user_id,
                    'user_type' => $user_type_id,
                ]);
            }

            if ($user && $is_new_emp_created) {
                return response()->json(['status' => 200,  'message' => 'Employee and User created successfully!'], 200);
            }

            return response()->json(['status' => 200,  'message' => 'Users created successfully!'], 200);

        } catch (QueryException $e) {
            // Handle the error and return a response
            return response()->json(['error' => 'Failed to create users: '.$e->getMessage()], 500);
        }

    }

    public function UserDataExport(Request $request)
    {
        $Usertype = $request->usertype;
        $search = $request->search;

        $datacount = User::where(function ($query) use ($Usertype) {
            if (! empty($Usertype)) {
                $query->where('usertype', $Usertype);

            }
        })->count();
        $randomstring = Str::random(10);
        $filepath = 'Data/AllUsers'.$randomstring.'.xlsx';

        $finalMappingData = $this->userService->listRoleService();

        if ($datacount > config('DATA.EXPORT.LIMIT')) {

            VisibilityReportDownloadReport::insert([
                'user_id' => $this->userData->id,
                'file_name' => $filepath,
                'request' => json_encode($request->all()),
                'status' => '1',
                'created_at' => now(),
                'source' => 'User List View Export',
            ]);

            $log = ExcelDownloadLog::insert([
                'user_id' => $this->userData->id,
                'request' => json_encode($request->all()),
                'status' => '1',
                'created_at' => \Illuminate\Support\Carbon::now(),
                'source' => 'User List View Export',
            ]);
            $model = User::class;
            $headings = [
                'Name',
                'Middle Name',
                'Last Name',
                'Email',
                'Dob',
                'Mobile',
                'Address',
                'Pincode',
                'Adhar No',
                'Pan No',
                'Employee Code',
                // 'Created At',
            ];
            $querycolumn = [
                'name',
                'middle_name',
                'last_name',
                'email',
                'dob',
                'mobile',
                'address',
                'pincode',
                'adhar_no',
                'pan_no',
                'employee_code',
                // 'created_at',
            ];

            ExportLargeExcel::dispatch($model, $headings, $request->all(), $this->userData->id, 'User List View Export', $filepath, $querycolumn)->onQueue('LargeExcelExports');

            return response()->json([
                'status' => 200,
                'message' => 'Data is to large to download. Added to Queue You will get this file later in job list  ',
            ]);
        } else {

            if (config('dashboard_storage_disk') === 's3') {

                
                $s3Root = trim(env('AWS_ROOT'), '/'); 
                $s3FilePath = $s3Root . '/dashboard/storage/exports/' . basename($filepath);
        
                Excel::store(
                    new UserDataExport($request, $finalMappingData),
                    $s3FilePath,
                    's3'
                );
        
                ExcelDataExportLog($this->userData->id, $s3FilePath, 'userList', 'completed', $request->all());
                $downloadUrl = Storage::disk('s3')->temporaryUrl(
                    $s3FilePath,
                    now()->addMinutes(30)
                );
                
            } else {
                Excel::store(new UserDataExport($request, $finalMappingData), $filepath, 'public');
                ExcelDataExportLog($this->userData->id, $filepath, 'userList', 'completed', $request->all());
                $downloadUrl = Storage::disk('public')->url($filepath);
            }
            
            return response()->json([
                'status'  => 200,
                'message' => 'Users Data Exported Successfully',
                'link'    => $downloadUrl,
            ]);
        }
    }

    public function fetchUserDetails(Request $request)
    {

        $responseData = [];
        $requestData = $request->all();
        foreach ($requestData as $category => $identifiers) {
            $responseData[$category] = [];

            foreach ($identifiers as $identifierType => $values) {

                foreach ($values as $identifier) {

                    $user = null;

                    if ($identifierType === 'seller_code') {
                        $user = User::where('username', credential_encrypt($identifier))->select('*')->first();
                        $userAttributes = $user ? $user->toArray() : null;

                    } elseif ($identifierType === 'mobile_no') {
                        $user = User::where('username', credential_encrypt($identifier))->select('*')->first();
                        $userAttributes = $user ? $user->toArray() : null;

                    }
                    if ($user) {
                        $responseData[$category][$identifier] = [
                            'status' => true,
                            'data' => $userAttributes,

                        ];
                    } else {

                        $responseData[$category][$identifier] = [
                            'status' => false,
                            'data' => null,
                        ];
                    }
                }
            }
        }

        return $responseData;

    }

    public function updateProfile(Request $request)
    {
        $authId = Auth::id();

        $UserProfile = User::find($request->id);
        if (! $UserProfile) {
            return response()->json(['message' => 'User data not found.'], 404);
        }

        if ($authId != $request->id) {
            return response()->json(['message' => 'You are not authorized to update this profile.'], 403);
        }

        $validator = Validator::make($request->all(), [
            'profile_image' => 'nullable|image|mimes:jpeg,png,jpg,gif|max:5120',
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }

        $imagePath = $UserProfile->profile_image;

        if ($request->hasFile('profile_image')) {
            if ($UserProfile->profile_image) {
                Storage::disk('public')->delete($UserProfile->profile_image);
            }

            $imageFile = $request->file('profile_image');
            $imageFileName = 'image_'.time().'.'.$imageFile->getClientOriginalExtension();
            $imageFile->storeAs('user_profile', $imageFileName, 'public');
            $imagePath = 'user_profile/'.$imageFileName;
        }

        $UserProfile->profile_image = $imagePath;
        $UserProfile->save();
        $imageUrl = Storage::disk('public')->url($imagePath);

        return response()->json([
            'success' => 200,
            'return_data' => [
                'profile_image' => $imageUrl,
            ],
            'message' => 'Data updated successfully!',
        ]);
    }

    public function getReportingUsers(Request $request)
    {

        $reportingRole = DB::table('roles')
            ->where('name', $request->roleName)
            ->pluck('id')
            ->first();

        $modelIds = DB::table('model_has_roles')
            ->where('role_id', $reportingRole)
            ->pluck('model_id');

        $tempArr = [];
        foreach ($modelIds as $modelId) {
            $user = User::where('id', $modelId)->select('id', 'name')->first();
            if ($user) {
                $tempArr[] = $user;
            }
        }

        $output = [];

        foreach ($tempArr as $temp) {
            $output[] = [
                'id' => $temp['id'],
                'name' => credential_decrypt($temp['name']),
            ];
        }

        return $output;
    }

    public function getReportingUsersNew(Request $request)
    {
        $authenticatedUser = Auth::user();

        $reportingRole = DB::table('roles')
            ->where('name', $request->roleName)
            ->pluck('id')
            ->first();

        $modelIds = DB::table('model_has_roles')
            ->where('role_id', $reportingRole)
            ->pluck('model_id');

        $tempArr = [];
        $output = [];

        $authUserRole = $authenticatedUser->getRoleNames()->toArray();

        $usertypeOfRole = Role::select('id', 'name', 'user_type')->where('name', $request->roleName)->first();

        if ($request->roleName == $authUserRole[0]) {
            $user = User::where('id', $authenticatedUser->id)->select('id', 'name', 'employee_code')->where('status', 'Y')->first();
            if ($user) {
                $tempArr[] = $user;
            }
        } elseif ($authenticatedUser->is_admin == 'N' && ($authenticatedUser->usertype == $usertypeOfRole->user_type)) {
            $modelIdUsers = User::whereIn('id', $modelIds)->select('id', 'name','middle_name','last_name', 'reportingto', 'employee_code')->where('status', 'Y')->get();

            foreach ($modelIdUsers as $mu) {
                // if ($mu->reportingto == $authenticatedUser->id) {
                    $tempArr[] = $mu;
                // }
            }

            $userHierarcyofAuthenticatedUser = getUserLowerHierarchy($authenticatedUser->id, $authenticatedUser->usertype);
            $userHierarcyofAuthenticatedUserCollection = collect($userHierarcyofAuthenticatedUser);
            $mappedIdsOfAuthUser = $userHierarcyofAuthenticatedUserCollection->pluck('id');

            $authUserWithRoles = User::whereIn('id', $mappedIdsOfAuthUser)->select('id', 'name','middle_name','last_name', 'reportingto')->with('roles')->where('status', 'Y')->get();

            $storedIdsAndRoleIds = [];

            foreach ($authUserWithRoles as $user) {
                foreach ($user['roles'] as $role) {
                    $storedIdsAndRoleIds[] = [
                        'id' => $user['id'],
                        'role_id' => $role['id'],
                        'name' => implode(' ', array_filter([credential_decrypt($user['name']),credential_decrypt($user['middle_name']),credential_decrypt($user['last_name'])]))
                    ];
                }
            }

            $modelIdsArray = $modelIds->toArray();

            $filteredUsers = array_values(array_filter($storedIdsAndRoleIds, function ($user) use ($modelIdsArray) {
                return in_array($user['id'], $modelIdsArray);
            }));
            
            foreach ($tempArr as $temp) {
                $output[] = [
                    'id' => $temp['id'],
                    'name' => implode(' ', array_filter([credential_decrypt($temp['name']),credential_decrypt($temp['middle_name']),credential_decrypt($temp['last_name'])])),
                ];
            }
            $mergedArray = array_merge($output, $filteredUsers);
            $uniqueUsers = [];
            $seenIds = [];

            foreach ($mergedArray as $user) {
                if (! in_array($user['id'], $seenIds)) {
                    $seenIds[] = $user['id']; // Mark this ID as seen
                    $uniqueUsers[] = $user; // Add the user to uniqueUsers
                }
            }
            $formatedArray = [];
            foreach ($uniqueUsers as $u) {
                $formatedArray[] = [
                    'id' => $u['id'],
                    'name' => $u['name'].' ('.User::where('id', $u['id'])->pluck('employee_code')->first().')', // here we are concatenating empcode of the user with name

                ];
            }

            return $formatedArray;

        } else {
            if (($authenticatedUser->is_admin == 'Y') || ($authenticatedUser->usertype != $usertypeOfRole->user_type)) {
                foreach ($modelIds as $modelId) {
                    $user = User::where('id', $modelId)->select('id', 'name','middle_name','last_name', 'employee_code')->where('status', 'Y')->first();
                    if ($user) {
                        $tempArr[] = $user;
                    }
                }
            }
        }

        foreach ($tempArr as $temp) {
            $output[] = [
                'id' => $temp['id'],
                'name' => implode(' ', array_filter([credential_decrypt($temp['name']),credential_decrypt($temp['middle_name']),credential_decrypt($temp['last_name'])])).' ('.$temp['employee_code'].')',
            ];
        }

        return $output;
    }

    public function editUsers(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'id' => 'required|exists:users,id', // Checks if 'id' exists in the 'users' table
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'errors' => $validator->errors(),
            ], 422);
        }

        $user = User::select('users.id', 'users.name', 'users.middle_name', 'users.last_name', 'users.dob', 'users.license_start_date', 'users.license_end_date', 'users.email', 'users.address', 'users.pincode', 'users.gender', 'users.usertype', 'users.mobile', 'users.username', 'users.reportingto', 'users.bank_branch', 'users.bank_name', 'users.bank_city', 'users.account_no', 'users.ifsc_code', 'users.account_holder_name', 'users.employee_code', 'users.pos_code', 'users.adhar_no', 'users.pan_no', 'users.zone_id', 'users.reportingto as parent_id', 'parent.username as parent_username', 'parent.name as parent_name', 'users.status', 'users.qualification', 'users.profile_image')->leftJoin('users as parent', 'users.reportingto', '=', 'parent.id')->where('users.id', $request->id)->first();

        $zoneData = ZoneMasterModel::where('id', $user['zone_id'])->value('office_zone');
        $roleName = Role::where('id', $user['reportingto'])->value('name');
        $userTypeDetails = userTypes::select('id', 'name', 'Identifier')->where('id', $user['usertype'])->first();

        $roleId = DB::table('model_has_roles')->where('model_id', $user['id'])->value('role_id');

        $roleDetails = Role::where('id', $roleId)->select('id', 'name')->first();

        $qualificationData = QualificationMaster::select('qualification_master_id as id', 'qualification_name as name')->where('qualification_master_id', $user['qualification'])->get();

        $userlobData = SellNow::select('lob_id')->where('user_id', $request->id)->get();
        $lobIdArray = $userlobData->pluck('lob_id');

        $lobName = lobMaster::whereIn('id', $lobIdArray)->select('id', 'lob')->get();

        $usersData[] = [
            'id' => $user['id'],
            'name' => credential_decrypt($user['name']),
            'middle_name' => credential_decrypt($user['middle_name']),
            'last_name' => credential_decrypt($user['last_name']),
            'email' => credential_decrypt($user['email']),
            'address' => credential_decrypt($user['address']),
            'pincode' => credential_decrypt($user['pincode']),
            'mobile' => credential_decrypt($user['mobile']),
            'username' => credential_decrypt($user['username']),
            'parent_username' => credential_decrypt($user['parent_username']),
            'parent_name' => credential_decrypt($user['parent_name']),
            'gender' => $user['gender'],
            'bank_branch' => credential_decrypt($user['bank_branch']),
            'bank_name' => credential_decrypt($user['bank_name']),
            'bank_city' => credential_decrypt($user['bank_city']),
            'account_no' => credential_decrypt($user['account_no']),
            'ifsc_code' => credential_decrypt($user['ifsc_code']),
            'account_holder_name' => credential_decrypt($user['account_holder_name']),
            'employeeCode' => $user['employee_code'],
            'dob' => credential_decrypt($user['dob']) ?? '', // dob ka issue hay
            'license_start_date' => credential_decrypt($user['license_start_date']) ?? '',
            'license_end_date' => credential_decrypt($user['license_end_date']) ?? '',
            'zoneId' => [
                'id' => $user['zone_id'],
                'office_zone' => $zoneData,
            ],
            'reportingTo' => $user['reportingto'] ?? '',
            'reportingRole' => $roleName,
            'usertype' => [
                'id' => $user['usertype'],
                'name' => $userTypeDetails->name ?? '',
                'Identifier' => $userTypeDetails->Identifier ?? '',
            ],
            'lob_id' => $lobName ?? null,
            'role' => [
                'id' => $roleDetails->id ?? '',
                'name' => $roleDetails->name ?? '',
            ],
            'test_tag' => 'test',
            'adhar_no' => credential_decrypt($user['adhar_no']),
            'pan_no' => credential_decrypt($user['pan_no']),
            'qualification' => $qualificationData,
            'Status' => $user['status'] == 'Y' ? 'Active' : 'Inactive',
            'profile_image' => $user['profile_image']
            ? Storage::disk('public')->url($user['profile_image'])
            : null,
        ];

        if ($usersData != null) {
            return response()->json(
                [
                    'status' => 'true',
                    'data' => $usersData,
                    'message' => 'Data Found',

                ]
            );
        }

        return response()->json(
            [
                'status' => 'false',
                'data' => [],
                'message' => 'No Data Found',
            ]
        );
    }

    public function updateUserMaping(Request $request)
    {
        $request->validate([
            'file' => 'required|mimes:xlsx,xls,csv',
        ]);

        Excel::import(new UpdateUserMappingOneClick, $request->file('file'));

        return response()->json(['message' => 'Data imported successfully']);
    }
}
