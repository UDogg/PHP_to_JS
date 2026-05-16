<?php

namespace App\Http\Controllers;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Str;
use Illuminate\Support\Carbon;
use App\Models\lobMaster;
use App\Models\Customer;
use App\Models\User;
use App\Http\Controllers\User\LoginController;


class BclSSO extends Controller
{
    public function generateToken(Request $request)
    {
        $data = $request->json()->all();

        if (empty($data['username']) || empty($data['password'])) {
            return response()->json([
                'status'  => 'false',
                'message' => 'username & password field is required.',
                'token'   => ''
            ]);
        }

        $validUsername = config('bcl_sso_username');
        $validPassword = config('bcl_sso_password');

        if ($data['username'] !== $validUsername || $data['password'] !== $validPassword) {
            return response()->json([
                'status'  => 'false',
                'message' => 'Invalid username & password.',
                'token'   => ''
            ]);
        }

        $uuidToken = Str::uuid()->toString();

        $inserted = DB::table('login_api_tokens')->insert([
            'user_name'    => $data['username'],
            'access_token' => $uuidToken,
            'status'       => 'Y',
            'expires_at'   => Carbon::now()->addMinutes(30),
            'created_at'   => Carbon::now(),
            'updated_at'   => Carbon::now(),
        ]);

        if (! $inserted) {
            return response()->json([
                'status'  => 'false',
                'message' => 'Something went wrong. Please try again.',
                'token'   => ''
            ]);
        }

        $response = [
            'status'      => 'true',
            'token'       => $uuidToken,
            'expires_at'  => Carbon::now()->addMinutes(30)->format('d/m/Y h:i a'),
        ];

        $response['return_url'] = config('bcl_sso_return_url') . $uuidToken;
   
        return response()->json($response);
    }

    public function validateToken(Request $request)
    {
        $token = trim($request->query('token'));
        $lob   = trim($request->query('lob'));
        $flag1 = trim($request->query('Flag1'));

        $accessRights = DB::table('lob_master')
            ->where('is_enabled', 'Y')
            ->pluck('lob')
            ->filter()
            ->toArray();

        array_push($accessRights, 'Dashboard');
  
        $errors = [
            'token' => '',
            'lob'   => '',
            'Flag1' => '',
        ];

        if ($token === '') {
            $errors['token'] = 'Token field is required';
        }

        if ($lob === '') {
            $errors['lob'] = 'lob field is required';
        } elseif (! in_array($lob, $accessRights)) {
            $errors['lob'] = 'invaild lob. example : ' . implode(',', $accessRights);
        }

        if ($flag1 === '') {
            $errors['Flag1'] = 'lob field is required';
        }

        if ($errors['token'] || $errors['lob'] || $errors['Flag1']) {
            return response()->json([
                'status'  => false,
                'message' => 'validation error',
                'data'    => $errors,
            ]);
        }

        $token = str_replace('%20', '', $token);

        $tokenRow = DB::table('login_api_tokens')
            ->select('id', 'access_token', 'status', 'created_at', 'user_name')
            ->where([
                'access_token' => $token,
                'status'       => 'Y',
            ])
            ->first();


        if (! $tokenRow) {
            return response()->json([
                'status'  => false,
                'message' => 'Invalid Access Token.',
            ]);
        }

        $createdAt = Carbon::parse($tokenRow->created_at);
        $minutes   = $createdAt->diffInMinutes(Carbon::now());

        if ($minutes > 30) {
            return response()->json([
                'status'  => false,
                'message' => 'Token Expired.',
            ]);
        }else{

            DB::table('login_api_tokens')
                ->where('access_token', $token)
                ->update(['status' => 'N']);

            $result = token_verify_bcl($token, $flag1);

            if (!empty($result[0]['USERID'])) {

                $userdata = $result[0];              

                if($flag1 == "3"){
                    $encryptedUsername = credential_encrypt($userdata['Mobile']);
                    $user = DB::table('customers')
                    ->where('mobile', $encryptedUsername)
                    ->first();

                    if (!$user) {
                        // Create customer
                        $user = new Customer();
                        $user->mobile = $encryptedUsername;
                        $user->user_name = $encryptedUsername;
                        $user->save();

                        DB::table('model_has_roles')->insert([
                            'role_id' => 9,
                            'model_type' => 'App\Models\Customer',
                            'model_id' => $user->id
                        ]);

                        User::where('id', $user->id)
                        ->update([
                            'old_user_id' => $user->id,
                        ]);
                    }
                    $platform = 'customer';
                }else{
                    $encryptedUsername = credential_encrypt($userdata['USERID']);
                    $user = User::where('username', $encryptedUsername)->first();

                    $platform = 'user';
                    $EMPlogin = strtolower(config('EMP_login_for_bcl_sso'));
                        
                    if($EMPlogin == 'yes') {

                        if(!$user && $result[0]['UserLoginAs'] == 'EMP') {
    
                            $userdata = $result[0];
    
                            $fullName = trim($userdata['Name']);
                            $nameParts = explode(' ', $fullName, 2);
                            
                            $firstName = $nameParts[0] ?? '';
                            $lastName  = $nameParts[1] ?? '';
    
    
                            if (!empty($userdata['KeyAccountManager'])) {
                                $manager = User::where('username', credential_encrypt($userdata['KeyAccountManager']))->first();
                                if ($manager) {
                                    $reportingUserId = $manager->id;
                                }
                            }
                            $employee_type = 'EMP';
                            if($userdata['UserLoginAs'] == 'EMP' && in_array($userdata['UserType'],['SUB BROKER','PTE'])) {
                                $employee_type = 'PTE';
                            }
                            if($userdata['UserLoginAs'] == 'EMP' && $userdata['UserType']=='ASSOCIATE') {
                                $employee_type = 'ASSOCIATE';
                            }
                            
                            $user = new User();
                            $user->name        = credential_encrypt($firstName);
                            $user->last_name   = credential_encrypt($lastName);
                            $user->full_name   = $userdata['Name'];
                            $user->email       = credential_encrypt($userdata['Email']);
                            $user->username    = credential_encrypt($userdata['USERID']);
                            $user->mobile      = credential_encrypt($userdata['Mobile']);
                            $user->dob         = credential_encrypt($userdata['DOB']);
                            $user->password    = credential_encrypt("Pass@1234");
    
                            $user->gender      = $userdata['Gender'];
                            $user->status      = 'Y';
                            $user->usertype    = 1;
                            
                            $user->reportingto = $reportingUserId ?? null;
                            $user->region_name = $userdata['REGION_NAME'] ?? null;
                            $user->zone_name   = $userdata['ZONE_NAME'] ?? null;
                            $user->channel     = $userdata['Channel_name'] ?? null;
                            $user->branch_code = $userdata['BranchCode'] ?? null;
                            $user->employee_code    = $userdata['USERID'];
                            $user->employee_type    = $employee_type;
                            
                            $user->save();
                            $userId = $user->id;   
    
                            $user->old_user_id = $userId;
                            $user->save();  
    
                            $role = DB::table('roles')->where('name', 'Employee')->where('user_type', 1)->first();
                            if ($role) {
                                DB::table('model_has_roles')->insert([
                                    'role_id' => $role->id,
                                    'model_type' => 'App\Models\User',
                                    'model_id' => $user->id
                                ]);
                            }
    
                            $lobIds = DB::table('lob_master')
                            ->where('is_enabled', 'Y')
                            ->pluck('id')
                            ->toArray();
        
                            foreach ($lobIds as $lobId) {
                                DB::table('user_lob_relation')->insert([
                                    'user_id' => $user->id,
                                    'lob_id' => $lobId,
                                    'created_at' => Carbon::now(),
                                    'updated_at' => null,
                                ]);
                            }
                        }elseif($user) {

                            if($result[0]['UserLoginAs'] == 'EMP'){
                                $userdata = $result[0];
    
                                $fullName = trim($userdata['Name']);
                                $nameParts = explode(' ', $fullName, 2);
                                
                                $firstName = $nameParts[0] ?? '';
                                $lastName  = $nameParts[1] ?? '';
        
        
                                if (!empty($userdata['KeyAccountManager'])) {
                                    $manager = User::where('username', credential_encrypt($userdata['KeyAccountManager']))->first();
                                    if ($manager) {
                                        $reportingUserId = $manager->id;
                                    }
                                }
        
                                $employee_type = 'EMP';
                                if($userdata['UserLoginAs'] == 'EMP' && in_array($userdata['UserType'],['SUB BROKER','PTE'])) {
                                    $employee_type = 'PTE';
                                }
                                if($userdata['UserLoginAs'] == 'EMP' && $userdata['UserType']=='ASSOCIATE') {
                                    $employee_type = 'ASSOCIATE';
                                }
        
                                 User::where('id', $user->id)
                                 ->update([
                                    'name' => credential_encrypt($firstName),
                                    'last_name' => credential_encrypt($lastName),
                                    'full_name' => $userdata['Name'],
                                    'email' => credential_encrypt($userdata['Email']),
                                    'mobile' => credential_encrypt($userdata['Mobile']),
                                    'dob' => credential_encrypt($userdata['DOB']),
                                    'reportingto' => $reportingUserId ?? null,
                                    'region_name' => $userdata['REGION_NAME'] ?? null,
                                    'zone_name' => $userdata['ZONE_NAME'] ?? null,
                                    'channel' => $userdata['Channel_name'] ?? null,
                                    'branch_code' => $userdata['BranchCode'] ?? null,
                                    'employee_code' => $userdata['USERID'],
                                    'employee_type' => $employee_type,
                                 ]);
                            }elseif($result[0]['UserLoginAs'] == 'POSP'){
                                $userdata = $result[0];
    
                                $fullName = trim($userdata['Name']);
                                
                                User::where('id', $user->id)
                                ->update([
                                   'full_name' => $fullName,
                                ]);
                            }
                            
                        }
                    }
                    
                    if ($user && $result[0]['UserLoginAs'] == 'POSP' && $user->usertype != 2) {
                         
                        $mapping = DB::table('user_mappings')
                            ->where('user_id', $user->id)
                            ->where('user_type', 2)
                            ->first();
                        
                        if (!$mapping) {
                           return response()->json([
                                'status'  => false,
                                'message' => 'POSP User not found in system',
                            ]);
                        }else {
                            $user->usertype = 2;
                            $user->old_user_id = $mapping->old_user_id;
                            $user->employee_code = $mapping->employee_code;
                            $user->reportingto = $mapping->reportingto;
                        }
                    }

                    if ($user) {
                     \App\Models\User::where('id', $user->id)
                     ->update(['additional_data' => json_encode($userdata)]);
                    }
                }
            
                if ($user) {
                    
                    $otp = config('bcl_otp_for_bcl_sso'); 
                    $loginRequest = new Request([
                        'user_name' => credential_decrypt($user->username),
                        'otp' => $otp,
                        'loginOption' => 'email_otp',
                        'ip' => $request->ip(),
                        'browser' => $request->header('User-Agent'),
                        'platform' => $platform,
                        'UserLoginAs' => $result[0]['UserLoginAs'],
                    ]); 
            
                    $loginController = new LoginController();
                    $response = $loginController->verifyCustomerOtp($loginRequest);
                    $responseData = $response->getData(true);

                    if (isset($responseData['status']) && $responseData['status'] == 200 && !empty($responseData['access_token'])) {
                        $accessToken = $responseData['access_token'];

                        $type = DB::table('usertypes')
                            ->where('id', $user->usertype)
                            ->value('name');
                        
                        $redirectUrl = config('Profile.Frontend.Url') . '?xutm=' . $accessToken .'&type=' . $type;

                        return redirect()->away($redirectUrl, 301);

                    } else {
                        return response()->json([
                            "status" => false,
                            "message" => $responseData['message'] ?? 'Something went wrong.',
                            "return_url" => null
                        ]);
                    }
            
                } else {

                    return response()->json([
                        'status'  => false,
                        'message' => 'User not found in system',
                    ]);
                }
            }
        }
       
    }
}
