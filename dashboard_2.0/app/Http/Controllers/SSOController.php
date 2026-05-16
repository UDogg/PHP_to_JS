<?php

namespace App\Http\Controllers;

use App\Models\lobMaster;
use App\Models\PospIcMapping;
use App\Models\SSO;
use App\Models\TokenModel;
use App\Models\User;
use App\Models\UserDeactivateCounter;
use App\Models\UserAdditionalData;
use App\Models\userTypes;
use App\Models\masterCompany;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Validator;
use Carbon\Carbon;


// use GuzzleHttp\Client;
// use GuzzleHttp\Psr7\Request;
// use Illuminate\Http\Request;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Log;

class SSOController extends Controller
{

    /**
     * Show the form for creating a new resource.
     */
    public function create(Request $request)
    {
         $request->validate([
            'username'=>'required|string',
            'password'=>'required'
         ]);
         $username = $request->input('username');
         $password = $request->input('password');
         if ($username == config('sso_user_name') && $password == config('sso_passwprd')) {

            $uuidToken = Str::uuid()->toString();

            SSO::create([
                'sso_api_token'=>$uuidToken,
                'status'=>'Y'
            ]);

            logApiRequestResponse(
                'generate_login_token',
                'POST',
                $request->all(),
                [
                    'status' => 'success',
                    'message' => 'Token generated successfully.',
                    'token' => $uuidToken
                ],
                201,
                $request->headers->all()
            );

            return response()->json([
                'status' => 'success',
                'message' => 'Token generated successfully.',
                'token' => $uuidToken
            ], 201);
        }else{
            logApiRequestResponse(
                'generate_login_token',
                'POST',
                $request->all(),
                [
                    'status' => 'error',
                    'message' => 'Invalid Username & Password',
                ],
                401,
                $request->headers->all()
            );
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid Username & Password',
            ], 401);
        }

    }

    public function TokenValidate(Request $request)
    {
        $token  = $request->bearerToken();
        if (empty($token))
        {
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid Token',
            ], 401);
        }
//        $request->validate([
//            'formdata' => 'required'
//        ]);
        $sso_token = SSO::select('sso_api_token')->where('sso_api_token',$token)->where('status','Y')->first();
        $encKey = "3333"; //config('sso_encrypt_key') ;
        if(empty($sso_token)){
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid Token',
            ], 401);
        }
        else
        {
            $updatessoToken = SSO::where('sso_api_token',$sso_token)->update(['status'=>'N']);
        }
        $iv = "1234567890123456"; //substr($request->formdata,-16);
        $formdata = $request->formdata;
//        dd($formdata);
//        $formdata = substr($request->formdata,0,-16);
//        dump($formdata,$iv,$encKey);
//        $decrypted = openssl_decrypt(base64_decode($formdata), "AES-256-CBC", $encKey, 0, $iv);
//        dd($decrypted);
//        $data = json_decode($decrypted, true);
        $UserEmail = $formdata['email'];

        $usertypeIdentifier = '';
        if(!empty($formdata['usertype']) && in_array($formdata['usertype'],['employee','hr']))
        {
            $usertypeIdentifier = "E";
        }
        else
        {
            $usertypeIdentifier = "U";
        }
        $usertype = userTypes::select('id')->where('Identifier',$usertypeIdentifier)->first()['id'];
        $checkEmail = User::where('email',credential_encrypt($UserEmail))->where('usertype',$usertype)->first();
        $lastUserId = null;
        if(empty($checkEmail)){
            $userCreate = User::create([
                'name' => credential_encrypt($formdata['name']),
               'email' => credential_encrypt($formdata['email']),
                'password' => bcrypt('Admin@123'),
                'username' => credential_encrypt(str_replace(" ","_",$formdata['name'])),
                'mobile' => credential_encrypt($formdata['email']),
                'address' => credential_encrypt("mumbai"),
                'pincode' => credential_encrypt(123456),
                'gender' => "M",
                'usertype' =>  $usertype ?? '',
            ]);
            $lastUserId = $userCreate->id;
            if(in_array($formdata['usertype'],['employee','hr']))
            {
                $getRoleId = DB::table('roles')->select('id','name')->get();
                foreach($getRoleId as $key => $value)
                {
                    if($value->name == 'Employee' && $formdata['usertype'] == 'employee')
                    {
                        $roleId = $value->id;
                    }
                    elseif($value->name == 'HR' && $formdata['usertype'] == 'hr')
                    {
                        $roleId = $value->id;
                    }
                }
                $assignRole = DB::table('model_has_roles')->insert([
                    'role_id' => $roleId ?? '',
                    'model_type' => 'App\Models\User',
                    'model_id' => $lastUserId
                ]);
            }
            else
            {
                $getRoleId = DB::table('roles')->select('id')->where('name','Customer')->where('guard_name','sanctum')->first();
                $assignRole = DB::table('model_has_roles')->insert([
                    'role_id' => $getRoleId->id ?? '',
                    'model_type' => 'App\Models\User',
                    'model_id' => $lastUserId
                ]);
            }
            $lobs = lobMaster::select('id')->where('is_enabled','Y')->get();
            foreach($lobs as $lob)
            {
                $userLobMapping = DB::table('user_lob_relation')->insert([
                    'user_id' => $lastUserId,
                    'lob_id' => $lob->id
                ]);
            }
        }
        else
        {
            $lastUserId = $checkEmail->id;
        }
        if(empty($checkEmail))
        {
            foreach($formdata['corporate_id'] as $corporateId)
            {
                $userCorporateMapping = DB::table('corporate_user_mapping')->insert([
                    'corporate_id' => $corporateId,
                    'user_id' => $lastUserId
                ]);
            }
        }
        $userdata = User::find($lastUserId);
        if($formdata['landing_type'] == 'dashboard')
        {
            $generateToken = generateTokenAll($userdata);
            $frontendUrl = config(	'Broker.FrontendUrl.dashboard');
            return response()->json([
                'status' => 'success',
                'data' => [
                    'token' => $generateToken,
                    'user_id' => $lastUserId,
                    'frontend_url' => $frontendUrl.'?xutm='.$generateToken
                ]
            ]);
        }
        else
        {
            $termToken = $url = '';

            if($formdata['landing_type'] == 'term')
            {
                $url = config('Broker.FrontendUrl.term');
            }
            else
            {
                $url = config('Broker.FrontendUrl.investment');
            }
            $lobId = lobMaster::select('id')->where('lob',$formdata['landing_type'])->first()['id'] ?? '';
            $XutmId = Str::uuid();
            $tokenStore = TokenModel::insert([
                'seller_id' => $lastUserId,
                'seller_type' => $usertypeIdentifier,
                'xutm' => $XutmId,
                'lob_id' => $lobId
            ]);
            $termFrontendUrl = $url."?token=".$XutmId;
            return response()->json([
                'status' => 'success',
                'data' => [
                    'user_id' => $lastUserId,
                    'frontend_url' => $termFrontendUrl
                ]
            ]);
        }

    }

    Public function ssoGenerateToken(Request $request){

        $user = Auth::user();
        $roleId = $user->roles->pluck('id')->first();
        $sellerType = userTypes::where('id',$user->usertype)->pluck('Identifier')->first();

        $client = new Client();
        $headers = [
            'Content-Type' => 'application/json'
        ];
        $body = json_encode([
                "username" => config("SSO_Commission_Username"),
                "password" => config('SSO_Commission_Password'),
        ]);
        $apiUrl = config('SSO_Commission_Token_Api');
        $methodType = 'POST';
        $request = new Ghttp($methodType, $apiUrl, $headers, $body);

        // Send the request asynchronously and wait for the response
        $response = $client->sendAsync($request)->wait();

        // Create the POST request with the correct method, URL, headers, and body
    //    $result = $response->getBody($apiUrl);
       $result = $response->getBody($apiUrl)->getContents();

       // Decode the JSON response into an associative array
       $data = json_decode($result, true); // Pass true to get an associative array
 
    if(config('store_api_logs') == true){
        logApiRequestResponse(
            $apiUrl,
            $methodType,
            json_decode($body, true),
            $data,
            $response->getStatusCode(),
            $headers
        );
    }

       $generatedToken = $data['data'];

        if($data['status'] == true){
            $headers = [
                'accept' => 'application/json',
                'Content-Type' => 'application/json'
            ];
            // $apiUrl = 'https://uatapibrokex.fynity.in/auth/validate_token';
            $apiUrl = config('SSO_Commission_Redirection_API');
            $methodType = 'POST';
            $body = [
                'token' => $generatedToken,
                'formData' => [[
                    'userDetails' => [
                        'seller_type' => $sellerType, 
                        'seller_username' => credential_decrypt($user->username),
                        'lob' => 'Dashboard',
                        'first_name' => credential_decrypt($user->name),
                        'last_name' => credential_decrypt($user->last_name),
                        'email_id' => credential_decrypt($user->email),
                        'user_id' => $user->id, 
                        'broker_id' => config('broker_id')??1, 
                        'role_id' => $roleId 
                    ],
                    'additional_info' => []
                ]]
            ];

            $jsonBody = json_encode($body);
            $request = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($request)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true); 
  
            if(config('store_api_logs') == true){
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers
                );
            }

            if($result){
                return  $data;
            }else{
                return response()->json([
                    'status' => 'failed',
                    'message' => "Token Generation failed",
                    'statusCode' => 500
                ]);
            }
        }
        else{
            return response()->json([
                'status' => 'failed',
                'message' => "Token Generation failed",
                'statusCode' => 500
            ]);
        }
        
    }
    public function generate(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'username' => 'required|string|max:50',
            'password' => 'required|string|max:50',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'false',
                'errors' => $validator->errors(),
            ], 422);
        }

        if (
            $request->username !== 'HEROPRODSSO' ||
            $request->password !== 'M9r0HL8sRado'
        ) {
            return response()->json([
                'status' => 'false',
                'message' => 'Invalid credentials.',
            ], 401);
        }

        $token = Str::uuid()->toString();

        $record = new SSO();
        $record->sso_api_token = $token;
        $record->formData = json_encode($request->only('username'));
        $record->status = 'Y';
        $record->created_at = now();
        $record->save();

        return response()->json([
            'status' => 'true',
            'token' => $token,
            'expires_at' => Carbon::now()->addMinute(30)->format('d/m/Y h:i a'),
        ]);
    }
    public function loginTokenValidate(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'access-token' => 'required|uuid',
            'formdata' => 'required|string',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'message' => 'Validation error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        $token = $request->input('access-token');
        $formdata = $request->input('formdata');

        $record = SSO::where('sso_api_token', $token)->where('status', 'Y')->first();

        if (!$record) {
            return response()->json([
                'status' => false,
                'message' => 'Invalid or expired access token.',
            ]);
        }

        if ($record->created_at && $record->created_at->diffInMinutes(now()) > 30) {
            return response()->json([
                'status' => false,
                'message' => 'Access token has expired.',
            ]);
        }

        // Invalidate token
        $record->update(['status' => 'N']);

        try {
            $decryptedData = $this->decryptFormdata($formdata);
            $userData = json_decode($decryptedData, true);
        } catch (\Exception $e) {
            return response()->json([
                'status' => false,
                'message' => 'Unable to decrypt form data.',
            ]);
        }

        if (empty($userData) || empty($userData['user_details']['seller_username'])) {
            return response()->json([
                'status' => false,
                'message' => 'Invalid user request data.',
            ]);
        }

        $encryptedMobile = credential_encrypt($userData['user_details']['seller_username']);
        $user = User::where('mobile', $encryptedMobile)->first();

        if (!$user) {
            return response()->json([
                'status' => false,
                'message' => 'User not found.',
            ]);
        }

        $lob = $userData['user_details']['lob'] ?? null;
        $sellerType = $userData['user_details']['seller_type'] ?? null;

        if ($lob === 'Dashboard') {
            $authToken = generateTokenAll($user);
            $frontendUrl = config('Profile.Frontend.Url');
            $url = $frontendUrl . '?xutm=' . $authToken;
        
        } elseif (in_array($lob, ['Car', 'Bike', 'Cv', 'Health'])) {
            $lobRecord = lobMaster::where('lob_master_name', strtoupper($lob))->first();
        
            if (!$lobRecord) {
                return response()->json([
                    'status' => false,
                    'message' => 'LOB record not found.',
                ]);
            }
        
            $generatedToken = (string) Str::uuid();
         
        
            TokenModel::create([
                'seller_id' => $user->id,
                'seller_type' => $sellerType,
                'xutm' => $generatedToken,
                'lob_id' => (string)$lobRecord->id??'',
            ]);
        
            $paramKey = strtolower($lob) === 'health' ? 'token' : 'xutm';
            $url = $lobRecord->frontend_url . '?' . $paramKey . '=' . $generatedToken;
        
        } else {
            return response()->json([
                'status' => false,
                'message' => 'Unsupported LOB type.',
            ]);
        }
        

        return response()->json([
            'status' => true,
            'message' => 'URL generated successfully.',
            'return_url' => $url,
        ]);
    }

    public function loginToValidateAU(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'access-token' => 'uuid',
            'formdata.entity_name' => 'required|string|max:255',
            'formdata.email'       => 'email',
            'formdata.name'        => 'max:255',
            'formdata.employee_code' => 'required|string|max:50',
            'formdata.landing_type'  => 'required|string',
            'formdata.seller_type'   => 'required|string|in:E,P,SP',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'message' => 'Validation error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        // $token = $request->input('access-token');

        // $record = SSO::where('sso_api_token', $token)->where('status', 'Y')->first();
        
        // if (!$record) {
        //     return response()->json([
        //         'status' => false,
        //         'message' => 'Invalid or expired access token.',
        //     ]);
        // }

        // if ($record->created_at && $record->created_at->diffInMinutes(now()) > 30) {
        //     return response()->json([
        //         'status' => false,
        //         'message' => 'Access token has expired.',
        //     ]);
        // }

        // // Invalidate token
        // $record->update(['status' => 'N']);

        $userData = $request->input('formdata');

        if (empty($userData['email'])) {
            return response()->json([
                'status' => false,
                'message' => 'Invalid user request data.',
            ]);
        }

        $encryptedEmployeeCode = credential_encrypt($userData['employee_code']);
        $user = User::where('username', $encryptedEmployeeCode)->where('status','Y')->first();
        

        if (!$user) {
            return response()->json([
                'status' => false,
                'message' => 'User not found.',
            ]);
        }

        $userDeactiveCount = UserDeactivateCounter::where('user_id', $user->id)->count();

        if($user->status=='N' && $userDeactiveCount==3){
            return response()->json([
                'status' => false,
                'message' => 'User is deactivated due to inactivity.',
            ]);
        }

        $lob = $userData['landing_type'] ?? null;
        $userSellerType = userTypes::where('id', $user->usertype)->pluck('name')->first();
        $sellerType = $userSellerType->Identifier ?? null;
        $sellerTypeName = $userSellerType->name ?? 'Employee';
        if ($lob === 'Dashboard') {
            $authToken = generateTokenAll($user);
            $frontendUrl = config('Profile.Frontend.Url');
            $url = $frontendUrl . '?xutm=' . $authToken.'&type='.$sellerTypeName.'&flow=dashboard';
        
        } elseif (in_array($lob, ['Car', 'Bike', 'Cv', 'Health'])) {
            $lobRecord = lobMaster::where('lob_master_name', strtoupper($lob))->first();
            if (!$lobRecord) {
                return response()->json([
                    'status' => false,
                    'message' => 'LOB record not found.',
                ]);
            }
        
            $generatedToken = (string) Str::uuid();
         
        
            TokenModel::create([
                'seller_id' => $user->id,
                'seller_type' => $sellerType,
                'xutm' => $generatedToken,
                'lob_id' => (string)$lobRecord->id??'',
            ]);
        
            $paramKey = strtolower($lob) === 'health' ? 'token' : 'xutm';
            $url = $lobRecord->frontend_url . '?' . $paramKey . '=' . $generatedToken;
        
        } else {
            return response()->json([
                'status' => false,
                'message' => 'Unsupported LOB type.',
            ]);
        }
        

        return response()->json([
            'status' => true,
            'message' => 'URL generated successfully.',
            'return_url' => $url,
            'user_data' => [
                'users_id' => credential_decrypt($user->id),
                'employee_code' => credential_decrypt($user->employee_code),
                'name' => credential_decrypt($user->name),
                'email' => credential_decrypt($user->email),
                'mobile' => credential_decrypt($user->mobile),
                'aadhar_no' => credential_decrypt($user->adhar_no),
                'pan_no' => credential_decrypt($user->pan_no),
                'date_of_joining' => $user->userAdditionalData->date_of_joining ?? '',
                'department_code' => $user->userAdditionalData->department_code ?? '',
                'is_sp' => $user->userAdditionalData->is_sp ?? '',
                'sp_name' => $user->userAdditionalData->sp_name ?? '',
                'sp_urnno' => $user->userAdditionalData->sp_urnno ?? '',
                'sp_code' => $user->userAdditionalData->sp_code ?? '',
                'sp_certificate_date' => $user->userAdditionalData->sp_certificate_date ?? '',
                'certificate_valid_from' => $user->userAdditionalData->certificate_valid_from ?? '',
                'certificate_valid_till' => $user->userAdditionalData->certificate_valid_till ?? '',
            ]
        ]);
    }

    public function loginToValidateAUMotor(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'entity_name' => 'string|max:255',
            'email'       => 'email',
            'name'        => 'max:255',
            'employee_code' => 'string|max:50',
            'seller_type'   => 'string',
            'landing_type' => 'string'
        ]);

        if ($validator->fails()) {
            logApiRequestResponse(
                'SSO Login to Motor',
                'POST',
                $request->all(),
                [
                    'status' => false,
                    'message' => 'Validation error.',
                    'errors' => $validator->errors(),
                ],
                422,
                '',
                'Login to Motor'
            );
            return response()->json([
                'status' => false,
                'message' => 'Validation error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        // $token = $request->input('access-token');

        // $record = SSO::where('sso_api_token', $token)->where('status', 'Y')->first();
        
        // if (!$record) {
        //     return response()->json([
        //         'status' => false,
        //         'message' => 'Invalid or expired access token.',
        //     ]);
        // }

        // if ($record->created_at && $record->created_at->diffInMinutes(now()) > 30) {
        //     return response()->json([
        //         'status' => false,
        //         'message' => 'Access token has expired.',
        //     ]);
        // }

        // Invalidate token
        // $record->update(['status' => 'N']);

        // $userData = $request->input('formdata');

        if (empty($request->input('email'))) {
            logApiRequestResponse(
                'SSO Login to Motor',
                'POST',
                $request->all(),
                [
                    'status' => false,
                    'message' => 'Invalid user request data.',
                ],
                422,
                '',
                'Login to Motor'
            );
            return response()->json([
                'status' => false,
                'message' => 'Invalid user request data.',
            ]);
        }

        $encryptedEmployeeCode = credential_encrypt($request->input('employee_code'));
        $encryptedEmailId = credential_encrypt($request->input('email'));
        $user = User::with(['userAdditionalData','userBranchRelation'])
                ->where('users.status', 'Y')
                ->where(function ($query) use ($encryptedEmployeeCode, $encryptedEmailId) {
                    $query->where('username', $encryptedEmployeeCode)
                        ->orWhere('email', $encryptedEmailId);
                })
                ->first();


        if (!$user) {
            logApiRequestResponse(
                'SSO Login to Motor',
                'POST',
                $request->all(),
                [
                    'status' => false,
                    'message' => 'User not found.',
                ],
                422,
                '',
                'Login to Motor'
            );
            return response()->json([
                'status' => false,
                'message' => 'User not found.',
            ]);
        }

        $userDeactiveCount = UserDeactivateCounter::where('user_id', $user->id)->count();

        if($user->status=='N' && $userDeactiveCount==3){
            return response()->json([
                'status' => false,
                'message' => 'User is deactivated due to inactivity.',
            ]);
        }

        $lob = $request->input('landing_type') ?? 'Dashboard';
        $sellerType = $request->input('seller_type') ?? null;
        $userSellerType = userTypes::where('id', $user->usertype)->pluck('name')->first();
        $sellerType = $userSellerType->Identifier ?? null;
        $sellerTypeName = $userSellerType->name ?? 'Employee';
        if ($lob === 'Dashboard') {
            $authToken = generateTokenAll($user);
            $frontendUrl = config('Profile.Frontend.Url');
            $url = $frontendUrl . '?xutm=' . $authToken.'&type='.$sellerTypeName;
        
        } elseif (in_array($lob, ['Car', 'Bike', 'Cv', 'Health'])) {
            $lobRecord = lobMaster::where('lob_master_name', strtoupper($lob))->first();
            if (!$lobRecord) {
                logApiRequestResponse(
                    'SSO Login to Motor',
                    'POST',
                    $request->all(),
                    [
                        'status' => false,
                        'message' => 'LOB record not found.',
                    ],
                    422,
                    '',
                    'Login to Motor'
                );
                return response()->json([
                    'status' => false,
                    'message' => 'LOB record not found.',
                ]);
            }
        
            $generatedToken = (string) Str::uuid();
         
        
            TokenModel::create([
                'seller_id' => $user->id,
                'seller_type' => $sellerType,
                'xutm' => $generatedToken,
                'lob_id' => (string)$lobRecord->id??'',
            ]);
        
            $paramKey = strtolower($lob) === 'health' ? 'token' : 'xutm';
            $url = $lobRecord->frontend_url . '?' . $paramKey . '=' . $generatedToken;
        
        } else {
            logApiRequestResponse(
                'SSO Login to Motor',
                'POST',
                $request->all(),
                [
                    'status' => false,
                    'message' => 'Unsupported LOB type.',
                ],
                422,
                '',
                'Login to Motor'
            );
            return response()->json([
                'status' => false,
                'message' => 'Unsupported LOB type.',
            ]);
        }

        $companyList = masterCompany::get();
        
        $sp_details = [];
        $branch_code = User::select('au_branch_dump.branchcode AS branch_code')->leftjoin('user_branch_relation', 'user_branch_relation.user_id', 'users.id')
            ->leftjoin('au_branch_dump', 'au_branch_dump.branchid', 'user_branch_relation.branch_id')
            ->where('users.id', $user->id)->first()->branch_code;    
        if($user->userAdditionalData->is_sp=='N'){

            $today = Carbon::now();

            $sp_details = UserAdditionalData::join('users','users.id','=','user_additional_data.user_id')
            ->leftjoin('user_branch_relation', 'user_branch_relation.user_id', 'users.id')
            ->leftjoin('au_branch_dump', 'au_branch_dump.branchid', 'user_branch_relation.branch_id')
            ->leftjoin('posp_ic_mappings', 'posp_ic_mappings.user_id', 'users.id')
            ->where('users.status', 'Y')
            ->where('is_sp', 'Y')
            ->where('au_branch_dump.branchcode', $branch_code)
            ->whereDate('certificate_valid_from', '<=', $today)
            ->whereDate('certificate_valid_till', '>=', $today)
            ->select('users.id as users_id', 'users.employee_code', 'users.email','users.mobile', 'sp_name','users.pan_no', 'users.adhar_no as aadhar_no', 'sp_urnno', 'sp_code',
            'au_branch_dump.branchcode AS sp_branch_code','sp_certificate_date', 'certificate_valid_from', 
            'certificate_valid_till','posp_ic_mappings.*')->get();
            
            foreach ($sp_details as &$sp_details_value) {
                unset($sp_details_value->id);
                unset($sp_details_value->user_id);
                unset($sp_details_value->ic);
                unset($sp_details_value->created_at);
                unset($sp_details_value->updated_at);
                $sp_details_value->email = credential_decrypt($sp_details_value->email);
                $sp_details_value->mobile = credential_decrypt($sp_details_value->mobile);
                $sp_details_value->pan_no = credential_decrypt($sp_details_value->pan_no);
                $sp_details_value->aadhar_no = credential_decrypt($sp_details_value->aadhar_no);
    
                foreach ($companyList as $c) {
                    $short = $c->company_shortname;
                    if (!empty($sp_details_value->{$short})) {
                        $sp_details_value->{"relation_{$short}"} = $sp_details_value->{$short};
                        unset($sp_details_value->{$short});
                    }
                }
            }
        }

        $user_data = [
            'users_id' => credential_decrypt($user->id),
            'employee_code' => credential_decrypt($user->employee_code),
            'name' => credential_decrypt($user->name),
            'email' => credential_decrypt($user->email),
            'mobile' => credential_decrypt($user->mobile),
            'date_of_joining' => $user->userAdditionalData->date_of_joining ?? '',
            'department_code' => $user->userAdditionalData->department_code ?? '',
            'is_sp' => $user->userAdditionalData->is_sp ?? 'N',
            'sp_name' => $user->userAdditionalData->sp_name ?? '',
            'sp_urnno' => $user->userAdditionalData->sp_urnno ?? '',
            'sp_code' => $user->userAdditionalData->sp_code ?? '',
            'branch_code' => $branch_code ?? '',
            'sp_certificate_date' => $user->userAdditionalData->sp_certificate_date ?? '',
            'certificate_valid_from' => $user->userAdditionalData->certificate_valid_from ?? '',
            'certificate_valid_till' => $user->userAdditionalData->certificate_valid_till ?? '',
            
        ];

        if($user->userAdditionalData->is_sp=='Y'){
            $ic_mapping_data = PospIcMapping::where('user_id', $user->id)->first();
            foreach ($companyList as $c) {
                $short = $c->company_shortname;
                if (!empty($ic_mapping_data->{$short})) {
                    $user_data["relation_{$short}"] = $ic_mapping_data->{$short};
                }
            }
        }
        $user_data['sp_details'] = $sp_details;

        logApiRequestResponse(
            'SSO Login to Motor',
            'POST',
            $request->all(),
            [
                'status' => true,
                'message' => 'URL generated successfully.',
                'return_url' => $url,
                'user_data' => $user_data
            ],
            200,
            '',
            'Login to Motor'
        );
        
        return response()->json([
            'status' => true,
            'message' => 'URL generated successfully.',
            'return_url' => $url,
            'user_data' => $user_data
        ]);
    }

    public function loginToValidateEncrypted(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'access-token' => 'required|uuid',
            'formdata' => 'required|string',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'message' => 'Validation error.',
                'errors' => $validator->errors(),
            ], 422);
        }

        $token = $request->input('access-token');
        $formdata = $request->input('formdata');

        $record = SSO::where('sso_api_token', $token)->where('status', 'Y')->first();
        
        if (!$record) {
            return response()->json([
                'status' => false,
                'message' => 'Invalid or expired access token.',
            ]);
        }

        if ($record->created_at && $record->created_at->diffInMinutes(now()) > 30) {
            return response()->json([
                'status' => false,
                'message' => 'Access token has expired.',
            ]);
        }

        // Invalidate token
        $record->update(['status' => 'N']);

        try {
            $decryptedData = $this->encryptDecryptFormData($formdata);
            $userData = !is_array($decryptedData) ? json_decode($decryptedData, true): $decryptedData;
        } catch (\Exception $e) {
            return response()->json([
                'status' => false,
                'message' => 'Unable to decrypt form data.',
            ]);
        }

        if (empty($userData) || empty($userData['email'])) {
            return response()->json([
                'status' => false,
                'message' => 'Invalid user request data.',
            ]);
        }

        $encryptedEmployeeCode = credential_encrypt($request->input('employee_code'));
        $user = User::where('username', $encryptedEmployeeCode)->first();
        

        if (!$user) {
            return response()->json([
                'status' => false,
                'message' => 'User not found.',
            ]);
        }

        $lob = $userData['landing_type'] ?? null;
        $sellerType = $userData['seller_type'] ?? null;
        if ($lob === 'Dashboard') {
            $authToken = generateTokenAll($user);
            $frontendUrl = config('Profile.Frontend.Url');
            $url = $frontendUrl . '?xutm=' . $authToken;
        
        } elseif (in_array($lob, ['Car', 'Bike', 'Cv', 'Health'])) {
            $lobRecord = lobMaster::where('lob_master_name', strtoupper($lob))->first();
            if (!$lobRecord) {
                return response()->json([
                    'status' => false,
                    'message' => 'LOB record not found.',
                ]);
            }
        
            $generatedToken = (string) Str::uuid();
         
        
            TokenModel::create([
                'seller_id' => $user->id,
                'seller_type' => $sellerType,
                'xutm' => $generatedToken,
                'lob_id' => (string)$lobRecord->id??'',
            ]);
        
            $paramKey = strtolower($lob) === 'health' ? 'token' : 'xutm';
            $url = $lobRecord->frontend_url . '?' . $paramKey . '=' . $generatedToken;
        
        } else {
            return response()->json([
                'status' => false,
                'message' => 'Unsupported LOB type.',
            ]);
        }
        

        return response()->json([
            'status' => true,
            'message' => 'URL generated successfully.',
            'return_url' => $url,
        ]);
    }

    public function encryptDecryptFormData($formdata)
    {
        $encrypted = $formdata;
        try {
            $decrypted = getDecryptedPayload($encrypted);
            $result = !is_array($decrypted) ? json_decode($decrypted, true) : $decrypted;

        } catch (\Exception $e) {
            $result = 'Decryption failed: ' . $e->getMessage();
        }

        return $result;
    }    

    private function decryptFormdata($formdata)
    {
        $encryption_key = 'Mt7654Hjkgtpk&6jhypolkcFtyG2';
        // $encryption_key = 'Dt4563Hjkgtpk&6jhypolkcFtyM3';
        $key = hash('sha256', $encryption_key);

        $iv_length = 16;

        // Extract IV from end of formdata
        $iv = substr($formdata, -$iv_length);
        // $iv = substr(hash('sha256', $iv), 0, 16);

        $encrypted = substr($formdata, 0, -$iv_length);

        $decodedEncrypted = base64_decode($encrypted);
  
        $decrypted = openssl_decrypt($decodedEncrypted, 'AES-256-CBC', $key, 0, $iv);

        return $decrypted;
    }
}
