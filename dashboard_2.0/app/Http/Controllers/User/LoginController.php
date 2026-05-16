<?php

namespace App\Http\Controllers\User;

use App\Events\EmailEvent;
use App\Events\SendOtpEvent;
use App\Exports\UserLoginReportExport;
use App\Http\Controllers\Controller;
use App\Http\Controllers\Plugins\PHPGangsta_GoogleAuthenticator;
use App\Mail\OTPVerificationMail;
use App\Mail\PasswordVerficationMail;
use App\Models\Broker;
use App\Models\delegateMasterModel;
use App\Models\lobMaster;
use App\Models\LoginHistory;
use App\Models\PersonalAccessTokens;
use App\Models\Otp;
use App\Models\OtpMaster;
use App\Models\QualificationMaster;
use App\Models\SellNow;
use App\Models\UiCustomization;
use App\Models\User;
use App\Models\EmailActivityLog;
use App\Models\Event;
use App\Models\SmsActivityLog;
use App\Models\SmsTemplate;
use App\Models\TemplateModel;
use App\Models\UserMapping;
use App\Models\ZoneMasterModel;
use Carbon\Carbon;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Mail;
use Illuminate\Support\Facades\Session;
use Illuminate\Support\Facades\Response;
use Illuminate\Support\Facades\Validator;
use App\Events\forgotpasswordEvent;
use App\Events\requestQrEvent;
use App\Exports\AllDataExport;
use App\Exports\loginHistoryExport;
use App\Models\UserAccessManagment;
use App\Models\userTypes;
use App\Models\Customer;
use App\Models\ThemeMaster;
use GrahamCampbell\ResultType\Success;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Storage;
use Laravel\Sanctum\PersonalAccessToken;
use Maatwebsite\Excel\Facades\Excel;
use Spatie\Permission\Models\Role;
use App\Models\CorporateDomainMapping;
use App\Models\corporatesOnBoardingMaster;
use App\Models\CorporateUserWhitelisting;
use App\Models\CustomerPolicyExpire;
use Str;


class LoginController extends Controller
{

    public function getUser(Request $request)
{
    $authUserId = Auth::id();

    $inactiveResponse = checkUserActivity($request);
    if ($inactiveResponse) {
        return $inactiveResponse;
    }

    $user = $request->user();
    $user_keys = [
        'name', 'middle_name', 'last_name', 'email', 'address', 'pincode', 'gender', 'usertype',
        'mobile', 'username', 'usertype', 'reportingto', 'profile_image'
    ];

    $user_details = [];
    foreach ($user_keys as $user_key) {
        $user_details[$user_key] = credential_decrypt($user->{$user_key});
    }

    if ($user->usertype == 0) {
        $user_details['usertype_name'] = 'Super Admin';
    } else {
        $usertype = userTypes::where('id', $user->usertype)->value('name');
        $user_details['usertype_name'] = $usertype;
    }

    if ($user->usertype == getUserTypeIdByIdentifier('U')) {
        $checkCustomer = CustomerPolicyExpire::where('customer_id', $user->id)->exists();
        if(config('AlwaysShowCustomerPopup')){
            $user_details['customerPolicyExpirePopup'] = true;
            $user_details['allowToSkip'] = $checkCustomer ? true : false;
        }else{
            $user_details['customerPolicyExpirePopup'] = $checkCustomer ? false : true;
        }
    }

    $user_details['isAdmin'] = $user->is_admin == "Y";

    if ($user->profile_image) {
        $user_details['profile_image'] = Storage::disk('public')->url($user->profile_image);
    } else {
        $user_details['profile_image'] = null;
    }

    $delegateCount = $user->Is_delegate == 'Y' ? $user->delegate_count : 0;
    $checkDelegate = delegateMasterModel::select('delegate_user_id', 'user_id')
        ->where('delegate_user_id', $user->id)
        ->get();

    $MainUsers = [];
    $user_details['SwitchDelegate'] = 'N';

    $rolename = null;
    $currentToken = $user->currentAccessToken();

    $userRoleAbility = collect($currentToken?->abilities ?? [])
        ->first(fn($ability) => is_string($ability) && str_starts_with($ability, "userRole:"));

    if (!empty($userRoleAbility)) {
        $parts = explode(":", $userRoleAbility);
        $roleId = $parts[1] ?? null;

        if ($roleId && is_numeric($roleId)) {
            try {
                $getRoleName = Role::findById($roleId, 'sanctum');
                $rolename = $getRoleName?->name ?? null;
            } catch (\Spatie\Permission\Exceptions\RoleDoesNotExist $e) {
                $rolename = DB::table('model_has_roles')
                    ->join('roles', 'roles.id', '=', 'model_has_roles.role_id')
                    ->where('model_has_roles.model_id', $user->id)
                    ->value('roles.name');
            }
        }
    }

    if (empty($rolename)) {
        $rolename = DB::table('model_has_roles')
            ->join('roles', 'roles.id', '=', 'model_has_roles.role_id')
            ->where('model_has_roles.model_id', $user->id)
            ->value('roles.name');
    }


    if ($checkDelegate->isNotEmpty()) {
        $getMainUsersOfDelegate = User::select('username', 'id')
            ->whereIn('id', $checkDelegate->pluck('user_id'))
            ->get();

        foreach ($getMainUsersOfDelegate as $key => $value) {
            $MainUsers[][$value->id] = credential_decrypt($value->username);
        }

        $user_details['SwitchDelegate'] = 'Y';
    }

    $currentToken = $request->user()->currentAccessToken();
    if (!$currentToken) {
        return requestResponseMessage([
            'status' => 500,
            'message' => config('Login.Error.Message') ?? 'Current token not found'
        ]);
    }

    $delegateData = null;
    $delegateInfo = null;

    if (is_array($currentToken->abilities) && isset($currentToken->abilities['delegate'])) {
        $delegateData = $currentToken->abilities['delegate'];
        $delegateInfo = [
            'delegate_user_id' => $delegateData['delegate_user_id'] ?? null,
            'delegate_username' => $delegateData['delegate_username'] ?? null,
        ];

        if (!$delegateInfo['delegate_user_id'] || !$delegateInfo['delegate_username']) {
            return requestResponseMessage([
                'status' => 500,
                'message' => 'Incomplete delegate data in token abilities'
            ]);
        }
    }

    $login = LoginHistory::where('user_id', $user->id)
        ->orderBy('created_at', 'desc')
        ->skip(1)
        ->first();

    $user_details['user_id'] = $user->id;
    $user_details['delegateData'] = $delegateData;
    !empty($MainUsers) ? $user_details['MainUsers'] = $MainUsers : null;
    !empty($delegateCount) ? $user_details['delegateCount'] = $delegateCount : null;
    !empty($delegateInfo) ? $user_details['delegateData'] = $delegateInfo : null;
    $user_details['last_login'] = $login ? Carbon::parse($login->created_at)->format('Y-m-d H:i:s') : null;
    $user_details['RoleName'] = $rolename;

    $user_type_from_mapping = [];
    $user_type_from_users = User::where('id', $user->id)->pluck('usertype')->toArray();

    if ($user->usertype != '5') {
        $user_type_from_mapping = UserMapping::where('user_id', $user->id)
            ->whereNot('user_type', 5)
            ->pluck('user_type')
            ->toArray();
    }

    $userTypeId = array_merge($user_type_from_users, $user_type_from_mapping);

    if (!empty($user_type_from_mapping)) {
        foreach ($userTypeId as $uti) {
            if ($user->usertype != $uti) {
                $userTypeName = userTypes::where('id', $uti)->pluck("name")->first();
                $user_details["multi_user"][] = [
                    "user_type_id" => $uti,
                    "user_type_name" => $userTypeName
                ];
            }
        }
    }

    $user_details['adhar_no'] = credential_decrypt($user->adhar_no);
    $user_details['name'] = $user_details['name'].' '.$user_details['middle_name'].' '.$user_details['last_name'];
    $user_details['pan_no'] = credential_decrypt($user->pan_no);
    $user_details['route'] = config('Redirect.on.login') ?? 'profile';

    $userLowerHierarchy = User::where("reportingto", $user->id)->exists();
    $user_details['user_hierarchy_flag'] = $userLowerHierarchy;

    $user = credential_decrypt($user);

    if ($user) {
        $response = [
            'status' => 200,
            'return_data' => $user_details,
            'message' => 'User Found',
        ];

        if ($request->loginOption != 'password') {
            $response['reset_password'] = false;
        } else {
            $checkLogin = LoginHistory::where('user_id', $user->id)
                ->where('logged_in_by', 'password')
                ->orderBy('created_at', 'desc')
                ->first();

            $response['reset_password'] = empty($checkLogin);
        }

        $response['return_data']['update_password'] = false;
        $response['return_data']['show_sell_now_or_pdf_popup']   = config('show_sell_now_or_pdf_popup')=="1" ? true : false;
        $sign_in_option = Broker::first()->sign_in_option;
        if ($sign_in_option && in_array('password', explode(',', $sign_in_option))) {
            $response['return_data']['update_password'] = true;
        }

        return response()->json($response, 200);
    } else {
        return response()->json([
            'status' => 500,
            'return_data' => [],
            'message' => config('Login.Error.Message') ?? 'User Not Found',
        ], 500);
    }
}


    public function customerLogout(Request $request)
    {
        $request->user()->currentAccessToken()->delete();
        return response()->json([
            'status' => 200,
            'return_data' => [],
            'message' => 'Logged out successfully'],
             200);
    }


    public function brokerData(Request $request)
    {
        if ($request->hasHeader('validation') && $request->header('validation')) {
            $token = $request->header('validation');
            $decryptedToken = getDecryptedPayload($token);

            $parts = explode('+', $decryptedToken);

            $url = $parts[0];      
            $time = $parts[1];

            $requestUri = $request->url();

            if ($requestUri != $url) {
                return response()->json([
                    'status' => false,
                    'message' => config('Login.Error.Message') ?? 'Invalid Source.'
                ], 400);
            }
    
            $currentTime = strtotime(date('H:i:s'));
            $extractedTime = strtotime($time);

            $diff = $currentTime - $extractedTime;

            if ($diff > 60) {
                return response()->json([
                    'status' => false,
                    'message' => config('Login.Error.Message') ?? 'Token expired.'
                ], 400);
            }

        }
        
        $theme_data = ThemeMaster::where('status', 'Y')
                ->where('user_id', 2)
                ->first();

            $brokerData = Broker::select('sign_in_option','broker_name','email','captacha_configure','logo','favicon_icon','created_at','updated_at','front_logo')->first();
            $broker = $brokerData ? $brokerData->toArray() : [];
            if (!empty($broker)) {
                $broker['captacha_configure'] = strtolower(trim($broker['captacha_configure'])) === 'on';
                $broker['logo_url'] = $this->makeFileUrl($brokerData->logo);
                $broker['favicon_icon_url'] = $this->makeFileUrl($brokerData->favicon_icon);
                $broker['front_logo_url'] = $this->makeFileUrl($brokerData->front_logo);
                $broker['color-primary'] = $theme_data['theme_value']['color-primary'] ?? '1 130 255';
                if(empty($brokerData->front_logo)){
                    $broker['front_logo_url'] = "";
                }
                unset($broker['logo']);
                unset($broker['favicon_icon']);
                unset($broker['front_logo']);
                $uiCustomization = UiCustomization::first();
                if ($uiCustomization) {
                    $broker['ui_customization'] = $uiCustomization->toArray();
                }
                $signInOption = explode(',', $broker['sign_in_option']);
                return response()->json(
                    [
                        'status' => 200,
                        'loginOption' => $signInOption,
                        'return_data' => $broker,
                        'message' => 'Data fetched successfully',
                    ],
                    200
                );
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'No data found for broker',
                    ],
                    500
                );
            }
    }
    public function customerLogin(Request $request)
    {   
        if ($request->boolean('loginConversion')) {
            $request->merge([
                'user_name' => getDecryptedPayload($request->input('user_name')),
                'password' => getDecryptedPayload($request->input('password')),
            ]);
        }
            $platform = $request->platform ?? null;

            if ($platform == 'customer') {

                $request->validate([
                    'user_name' => [
                        'nullable',
                        function ($attribute, $value, $fail) {
                            if (empty($value)) return;

                            if (
                                !filter_var($value, FILTER_VALIDATE_EMAIL) &&
                                !preg_match('/^[6-9]\d{9}$/', $value)
                            ) {
                                $fail('The ' . $attribute . ' must be a valid email or a 10-digit mobile number.');
                            }
                        },
                    ],
                ]);

                 if (config('Allow.Customer.Email.Login') == 'true') {

                    return $this->handleCustomerEmailLogin($request);
                } else {
                    $customerData = Customer::where('mobile', credential_encrypt($request->user_name))->first();
                }

                if ($customerData) {
                  return  $this->handleOtpSending($customerData);
                }else {
                    return response()->json([
                        'status' => 404,
                        'message' => config('Login.Error.Message') ?? 'Customer Credentials not found.',
                    ], 404);
                }

            } else {
                    $user = User::with([
                        'userType:id,name as usertype_name,is_active as usertype_status,Identifier',
                        'userMappings'
                    ])
                    ->where(function ($query) use ($request) {
                        $credential = credential_encrypt($request->user_name);
                        $query->where('username', $credential)
                            ->orWhere('email', $credential)
                            ->orWhere('mobile', $credential);
                    })
                    ->first();
                if (!$user) {
                    return response()->json([
                        'status' => 404,
                        'message' => config('Login.Error.Message') ?? 'Credentials not found.',
                    ], 404);
                }
                if (config('Deactivate.User.On.Inactivity') && $user->status=='N') {
                    return response()->json([
                        'status' => 404,
                        'message' => 'Your account has been deactivated due to inactivity. Please contact the administrator.'
                    ], 404);
                }
            }
        if ($request->loginOption == 'password') {
            $type = 'password';
            $request->merge(['type' => $type]);
            $rules = [
                'password' => ['required'],
                'user_name' => ['required'],
            ];

            $validator = Validator::make($request->all(), $rules);

            if ($validator->fails()) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'Validation fails',
                    'errors' => $validator->errors(),
                ], 500);
            }

            $response = validateUserTypeForPlatform($user, $platform);
            if ($response) {
                return $response;
            }
  
            if ($user) {
                if(($user->usertype_status) == 'N'){
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'User Type for this User is inactive',
                    ], 500);
                }
                if ($user->status !== 'Y') {
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'User is inactive',
                    ], 500);
                }

                if($user->usertype == 2 ){
                    $adharPanLinkStatus = $user->pan_link_status == 1 ? false : true;  // if user pan is not link then we are give true to frontend to display popup
                }

                $valid_user = Hash::check($request->password, $user->password);

                if ($valid_user) {
                    if(!empty($user->usertype))
                    {
                        $usertype = DB::table('usertypes')->select('name')->where('id',$user->usertype)->first();
                    }
                    else
                    {
                        $usertype = '';
                    }

                    $login = LoginHistory::where('user_id', $user->id)->where('logged_in_by','password')->orderBy('created_at', 'desc')
                    ->first();
                    if (empty($login)) {
                        $this->deleteExitsToken($user);

                        $token = generateTokenAll($user);
                        $cookie = cookie('token', $token, 60 * 24);
                        return response()->json([
                            'status' => 200,
                            'return_data' => ['reset_password' => true],
                            'access_token' => $token,
                            'message' => 'Please Reset Your Password',
                        ], 200)->withCookie($cookie);
                    } else {
                            if (config('concurrent_login')=="1") {
                                $login_count = $this->getUserTotalLoginCount($user->id);
                            }else{
                                $login_count=1;
                            }
                            $this->deleteExitsToken($user);
                            SaveLoginHistory($user, $request);
                            $token = generateTokenAll($user);
                            $cookie = cookie('token', $token, 60 * 24);
                            return response()->json([
                                'status' => 200,
                                'token_type' => 'Bearer',
                                'access_token' => $token,
                                'usertype' => $usertype->name ?? '',
                                'return_data' => [],
                                'message' => 'Login successfully',
                                'current_login_count' => $login_count,
                                'adharPanLinkStatus' => $adharPanLinkStatus ?? false,
                            ], 200)->withCookie($cookie);

                    }
                } else {
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'The provided credentials do not match our records',
                    ], 500);
                }
            } else {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'The provided credentials do not match our records or the user is deleted',
                ], 500);
            }
        }


        elseif ($request->loginOption == 'email_otp') {
            $rules = [
                'user_name' => ['required'],
            ];


            $validator = Validator::make($request->all(), $rules);

            if ($validator->fails()) {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'Validation failed',
                        'errors' => $validator->errors()
                    ],
                    500
                );
            }
 
          

            $response = validateUserTypeForPlatform($user, $platform);
            if ($response) {
                return $response;
            }
            
            if ($user) {
               return $this->handleOtpSending($user);

            } else {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'User Does Not Exist',
                ],500);
            }
        }elseif ($request->loginOption == 'totp') {
            $rules = [
                'user_name' => ['required', 'string'],
            ];
            $validator = Validator::make($request->all(), $rules);
            if ($validator->fails()) {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'validations fails',
                        'errors' => $validator->errors()
                    ],
                    500
                );
            } else {
                 
                

                    if ($user) {
                        if(($user->usertype_status) == 'N'){
                            return response()->json([
                                'status' => 500,
                                'return_data' => [],
                                'message' => config('Login.Error.Message') ?? 'User Type for this User is inactive',
                            ], 500);
                        }
                        if ($user->status !== 'Y') {
                            return response()->json([
                                'status' => 500,
                                'return_data' => [],
                                'message' => config('Login.Error.Message') ?? 'User is inactive',
                            ], 500);
                        }
                    return response()->json(
                        [
                            'status' => 200,
                            'return_data' => [],
                            'message' => 'Totp has been sent to your email',
                        ],
                        200
                    );
                }else{
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => config('Login.Error.Message') ?? 'Invalid User',
                        ],
                        500
                    );
                }

            }
        }
    }

    public function handleCustomerEmailLogin($request)
    {
        $customerData = Customer::where('email', credential_encrypt($request->user_name))->first() ?? null;
        $broker = Broker::first();
        $master_otp = $broker->master_otp;

        if (!$customerData) {
            $domainFromEmail = str::after($request->user_name, '@');

            $domainExists = corporatesOnBoardingMaster::whereRaw("FIND_IN_SET(?, company_domain)", [$domainFromEmail])
                ->where('status', 'Active')
                ->first(); // find in set ko change karna hay

            if (!$domainExists) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'coorporate is not onboarded or Active please connect with admin',
                ], 500);
            }

            $otp = mt_rand(100000, 999999);
            if ($request->has("otp")) {

                $whiteListedUser = CorporateUserWhitelisting::where('email', credential_encrypt($request->user_name))->first();

                if ((now() < $whiteListedUser->lockout_time) && ($request->otp != $master_otp)) {
                    return response()->json([
                        'status' => 429,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ??'Your Account has been locked,try again after.' . $whiteListedUser->lockout_time,
                    ], 429);
                }

                if (($request->otp == $whiteListedUser->otp) || ($request->otp == $master_otp)) {
                    // customer create
                    $customer_user = Customer::insertCustomer([
                        'first_name' => $request->user_name,
                        'email' => credential_encrypt($request->user_name),
                        'mobile' => null,
                        'username' => credential_encrypt($request->user_name),
                        'password' => Hash::make($whiteListedUser->otp),
                        'otp' => $whiteListedUser->otp,
                        'otp_count' => 0,
                        'otp_sent_at' => now(),
                        'otp_expiry' => now()->addMinutes(5),
                        'role_id' => 9, // Assuming role_id 9 is for customer
                        'usertype' => 5, // Assuming usertype 5 is for customer
                    ]);

                    if ($customer_user) {
                        $role_id = DB::table('roles')
                            ->where('user_type', 5)
                            ->pluck('id')
                            ->first();

                        $CustomerAssignRole = DB::table('model_has_roles')->insert([
                            'role_id' => $role_id,
                            'model_type' => 'App\Models\Customer',
                            'model_id' => $customer_user->id
                        ]);
                    }

                    $newCustomer = Customer::where('email', credential_encrypt($request->user_name))->first();

                    $newCustomer->update([
                        'otp_sent_at' => now(),
                        'lockout_time' => null,
                        'failed_login_attempts' => 0,
                    ]);
                    $this->deleteExitsToken($newCustomer);
                    SaveLoginHistory($newCustomer, $request);
                    $token = generateTokenAll($newCustomer);
                    $cookie = cookie('token', $token, 60 * 24);

                    return response()->json([
                        'status' => 200,
                        'access_token' => $token,
                        'token_type' => 'Bearer',
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'OTP is Verified',
                    ], 200)->withCookie($cookie);
                } else {
                    //Lockout mechanism
                    return $this->failedLoginAttempts($whiteListedUser, "Invalid Credentials ");
                }
            } else {
                $user_corporate = CorporateUserWhitelisting::create([
                    'corporate_id' => $domainExists->id,
                    'email' => credential_encrypt($request->user_name),
                    'mobile' => null,
                    'status' => 1,
                    'otp' => $otp,
                    'otp_sent_at' => Carbon::now()->subMinutes(30),
                    'failed_login_attempts' => 0,
                    'lockout_time' => null,
                ]);

                $user_corporate->usertype_status = 'Y';
                $user_corporate->status = 'Y';
                $user_corporate->usertype =  5;
                $user_corporate->pan_link_status =  1;

                $this->handleOtpSending($user_corporate);
            }

            return Response::json([
                'status' => 200,
                'return_data' => [],
                'message' => config('Login.Error.Message') ?? 'OTP Sent to Your Email',
            ], 200);
        } else {
            if ($request->has("otp")) {
                $newCustomer = $customerData;

                if (!$newCustomer) {
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'Invalid User',
                    ], 500);
                }
                if ((now() < $newCustomer->lockout_time) && ($request->otp != $master_otp)) {
                    return response()->json([
                        'status' => 429,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ??'Your Account has been locked,try again after.' . $newCustomer->lockout_time,
                    ], 429);
                }

                if ( ($request->otp != $master_otp) && ($request->otp != $newCustomer->otp)) {
                   return $this->FailedLoginAttempts($newCustomer,"Invalid Credentials ");
                }


                $newCustomer->update([
                    'otp_sent_at' => now(),
                    'lockout_time' => null,
                    'failed_login_attempts' => 0,
                ]);
                $this->deleteExitsToken($newCustomer);
                $token = generateTokenAll($newCustomer);
                $cookie = cookie('token', $token, 60 * 24);

                return response()->json([
                    'status' => 200,
                    'access_token' => $token,
                    'token_type' => 'Bearer',
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'OTP is Verified',
                ], 200)->withCookie($cookie);
            } else {
                $this->handleOtpSending($customerData);
                return response()->json([
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'customer Data Found',
                ], 200);
            }
        }
    }
    public function SetNewPassword(Request $request){
        $rules = [
            'password' => [
                'required',
                'string',
                'min:8',
                'regex:/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/'
            ],
            'confirm_password' => 'required|string|same:password',
        ];
        $messages = [
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
                'message' => $validator->errors(),
            ], 500);
        }else{
            $decodedToken = base64_decode($request->token);
            if (preg_match('/([^|]+)\|([^ ]+)/', $decodedToken, $matches)) {
                $email = $matches[1];
                $date = $matches[2];
                $currentDate = date('Y-m-d');
                if($currentDate < $date){
                    $user=User::where('email',credential_encrypt($email))->first();
                    if ($user) {
                        $user->update([
                            'password' => Hash::make($request->password),
                        ]);
                        return response()->json([
                            'status' => 200,
                            'return_data' => [],
                            'message' => 'Password Changed Successfully',
                        ], 200);
                    }else{
                        return response()->json([
                            'status' => 500,
                            'return_data' => [],
                            'message' => config('Login.Error.Message') ?? 'Invalid User',
                        ], 500);
                    }
                }else{
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'Token Expired',
                    ]);
                }
            } else {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'Invalid token',
                ], 500);
            }
        }

    }
    public function verifyCustomerOtp(Request $request)
    {

        $request->validate([
            'otp' => ['required', 'digits:6'],
        ]);

        if ($request->boolean('loginConversion')) {
            $request->merge([
                'user_name' => getDecryptedPayload($request->input('user_name')),
                'otp' => getDecryptedPayload($request->input('otp')),
            ]);
        }
        $platform = $request->platform ?? null;
        $type = 'email_otp';
        $request->merge(['type' => $type]);
        $metadata =[];
        if ($platform == 'customer') {
            if (config('Allow.Customer.Email.Login') == 'true') {
                  return  $this->handleCustomerEmailLogin($request);
            }

            $customerData = Customer::where('mobile', credential_encrypt($request->user_name))->orWhere('email',credential_encrypt($request->user_name))->first();
            if ($customerData) {
              return  $this->handleOtpToken($customerData,$request,$metadata);
            }else {
                return response()->json([
                    'status' => 404,
                    'message' => config('Login.Error.Message') ?? 'Customer Credentials not found.',
                ], 404);
            }

        }else{
            $user = User::with([
                        'userType:id,name as usertype_name,is_active as usertype_status,Identifier',
                        'userMappings'
                    ])
                    ->where(function ($query) use ($request) {
                        $credential = credential_encrypt($request->user_name);
                        $query->where('username', $credential)
                            ->orWhere('email', $credential)
                            ->orWhere('mobile', $credential);
                    })
                    ->first();
                if (!$user) {
                    return response()->json([
                        'status' => 404,
                        'message' => config('Login.Error.Message') ?? 'Credentials not found.',
                    ], 404);
                }

            
                $response = validateUserTypeForPlatform($user, $platform);
            if ($response) {
                return $response;
            }
            

            if ($user->userMappings->isNotEmpty() && $user->usertype !="1") {
                $user_usertype =  $user->userMappings[0]->user_type;
                $customerRoleId=$user->userMappings[0]->role_id;
                $metadata=["usertype:$user_usertype", "userRole:$customerRoleId","switch:false"];    
            }

            if ($user) {
            return  $this->handleOtpToken($user,$request,$metadata);
            }else{
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'Invalid User',
                ], 500);
            } 

        }
    }
    public function verifyCustomerTotp(Request $request)
    {
        $platform = $request->platform ?? null;
        $validator = Validator::make($request->all(), [
            'email' => 'required',
            'gauth_otp' => 'nullable | numeric',
        ]);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'validations fails',
                    'errors' => $validator->errors()
                ],
                500
            );
        }

        $email = $request->email;
        $user = User::where('email', $email)->first();

        if ($user->totp_secret != null) {
            $ga = new PHPGangsta_GoogleAuthenticator();
            $secret = credential_decrypt($user->totp_secret);
            $checkResult = $ga->verifyCode($secret, $request->gauth_otp, 2);
        } else {
            $checkResult = true;
        }
        if ($checkResult) {
            $credentials = [
                'email' => $user->email,
                'password' => $user->password,
            ];
            $this->deleteExitsToken($user);

            $token = generateTokenAll($user);
            $cookie = cookie('token', $token, 60 * 24);
            return response()->json([
                'status' => 200,
                'access_token' => $token,
                'token_type' => 'Bearer',
                'return_data' => [],
                'message' => 'TOTP is Verified',
            ], 200)->withCookie($cookie);
        } else {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => config('Login.Error.Message') ?? 'TOTP is Not Verified',
            ], 500);
        }
    }

    public function CustomerResendQrCode(Request $request){
        $validateData = [
            'user_name' => 'required|string'
        ];

        $validator = Validator::make($request->all(), $validateData);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'validations fails',
                    'errors' => $validator->errors()
                ],
                500
            );
        } else {
                $contentData = TemplateModel::where('event', 'Send OTP')->exists()
                ? TemplateModel::where('event', 'Request QR')->get()
                : TemplateModel::where('event', 'add_email_template')->get();

                $user = User::where('username',  credential_encrypt($request->user_name))->Orwhere('email', credential_encrypt($request->user_name))->Orwhere('mobile', credential_encrypt($request->user_name))->first();
                if($user){
                        foreach($contentData as $contentData) {
                            $title = $contentData->title ?? 'O T P Verification Mail';
                            $content = $contentData->content?? 'Please Add Template Content From Template';
                            $decodedContent = html_entity_decode($content);
                            $plainTextTitle = strip_tags($decodedContent);
                            $body = $plainTextTitle ?: 'Default Body';
                            $new_email = credential_decrypt($user->email);
                            $qrCode_generated = generateQrcode();
                            $qrcode =  $qrCode_generated['QrCode'];
                            $secret = $qrCode_generated['secret'];
                            $password = $user->password;
                            event(new requestQrEvent($new_email, $qrcode,$secret,$password,$body,$title));
                            EmailActivityLog::create([
                                'email' => $new_email,
                                'subject' => 'QR Code Resent',
                                'body' => 'QR Code Resent.',
                                'type' => 'QR Code Resent',
                                'status' => 'Email Sent',
                                'sent_at' => now(),
                            ]);
                            User::where('email', $new_email)->update([
                                'totp_secret' => credential_encrypt($qrCode_generated['secret'])
                            ]);


                        return response()->json([
                            'status' => 200,
                            'return_data' => [],
                            'message' => 'QR Code Resent',
                        ], 200);
                    }

                }else{
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'Invalid User',
                    ], 500);
                }

     }
    }
    public function login(Request $request)
    {
        $sign_in_option = Broker::first();
        $option = explode(',', $sign_in_option->sign_in_option);

        if ($request->loginOption == 'password') {
            $credentials = [
                'email' => credential_encrypt($request->email),
                'password' => $request->password,
            ];
            $rules = [
                'email' => ['required', 'email'],
                'password' => ['required', 'string'],
                'remember' => ['nullable', 'string', 'in:on'],
            ];
            $validator = Validator::make($request->all(), $rules);
            if ($validator->fails()) {
                return redirect()->back()->withErrors($validator->errors())->withInput();
            }
            $user = User::where('email', $credentials['email'])->first();
            if ($user) {
                $valid_user = Hash::check($credentials['password'], $user->password);
                if ($valid_user) {
                    $login = LoginHistory::where('user_id', $user->id)->first();
                    if (empty($login)) {
                        $user_id = $user->id;
                        return view('user.resetpassword', compact('user_id'));
                    } else {
                        if (Auth::attempt($credentials, $request->remember)) {
                            $this->deleteExitsToken($user);

                            SaveLoginHistory($user, $request);
                            $request->session()->regenerate();
                            $token = generateTokenAll($user);
                            return redirect()->intended('/')->withCookie('Token', $token);
                        }
                    }
                }
                return back()->withErrors([
                    'email' => 'The provided credentials do not match our records.',
                ])->withInput();
            }
            return back()->withErrors([
                'email' => 'The provided credentials do not match our records.',
            ])->withInput();
        }
        if ($request->loginOption == 'email_otp') {
            $this->sendOtp($request);
            return redirect()->route('auth.loginwithotp');
        }
        if ($request->loginOption == 'totp') {
            $email = $request->email;
            $user = User::where('email', $email)->first();
            if ($user) {
                $request->session()->put('user_email', $user->email);
                $this->deleteExitsToken($user);

                $token = generateTokenAll($user);
                // session()->put('user_email', $user->email);
                return response()->json(['message' => 'User email stored successfully.'])->withCookie(cookie('user_token', $token));
            } else {
                return redirect()->back()->withErrors(['User not found.']);
            }
        }
    }

    public function resetPassword(Request $request)
    {
        $rules = [
            'newpassword' => [
                'required',
                'string',
                'min:8',
                'regex:/[A-Z]/',
                'regex:/[a-z]/',
                'regex:/[0-9]/',
                'regex:/[@$!%*?&]/',


            ],
            // 'confirmpassword' => 'required|same:newpassword',
            'confirmpassword' => [
                'required',
                'string',
                'min:8',
                'regex:/[A-Z]/',
                'regex:/[a-z]/',
                'regex:/[0-9]/',
                'regex:/[@$!%*?&]/',

            ],
        ];
        $customMessages = [
            'newpassword.required' => 'New password is required.',
            'confirmpassword.required' => 'Confirm password is required.',
        ];

        // $validator = Validator::make($request->all(), $rules, $customMessages);
        $validator = Validator::make($request->all(), $rules, $customMessages);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }
        $user = user::find($request->user_id);
        if ($user) {
            $user->password = Hash::make($request->newpassword);
            $user->save();
        }
        Auth::login($user);
        SaveLoginHistory($user, $request);
        return redirect()->intended('/');
    }

    public function logout()
    {
        Auth::logout();
        return redirect()->route('login');
    }

    public function loginForm()
    {
        $uiCustomization = UiCustomization::first(); // Adjust as needed to get the correct instance
        $username = $uiCustomization ? $uiCustomization->username : '';
        $password = $uiCustomization ? $uiCustomization->password : '';
        $broker = Broker::select('sign_in_option','captacha_configure', 'broker_name')->first();
        $broker_name = $broker->broker_name;
        $sign_in_option = $broker->sign_in_option;

        if (Auth::user()) {
            return redirect()->route('dashboard');
        }
        return view('user.login', compact('sign_in_option', 'username', 'password', 'broker_name','broker'));
    }

    public function showOtpForm()
    {

        if (session()->has('user_email')) {
            return view('user.otpForm');
        } else {
            return redirect()->intended('admin');
        }
    }
    public function showTOtpForm()
    {
        if (session()->has('user_email')) {
            return view('auth.totpForm');
        } else {
            return redirect()->intended('admin');
        }
    }
    public function verifyOtp(Request $request)
    {

        $request->validate([
            'otp' => 'required|numeric',
        ]);
        $user = User::where('otp', $request->input('otp'))->first();
        if (!$user) {
            return redirect()->back()->withErrors(['otp' => 'Invalid OTP']);
        }
        if ($user->otp != $request->input('otp')) {
            return response()->json([
                'success' => false,
                'message' => 'Invalid OTP.',
            ]);
        }

        Auth::login($user);
        return redirect()->intended('/');
    }

    public function verifyTOtp(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'gauth_otp' => 'nullable | numeric',
        ]);

        if ($validator->fails()) {
            return back()->withErrors($validator->errors());
        }
        $email = session('user_email');
        $user = User::where('email', $email)->first();

        if ($user->totp_secret != null) {
            // include_once app_path() . '/Helpers/PersonalDataEncryptionHelper.php';
            $ga = new PHPGangsta_GoogleAuthenticator();
            $secret = credential_decrypt($user->totp_secret);
            $checkResult = $ga->verifyCode($secret, $request->gauth_otp, 2);
        } else {
            $checkResult = true;
        }

        if ($checkResult) {
            $credentials = [
                'email' => $user->email,
                'password' => $user->password,
            ];
            Auth::login($user);
            $request->session()->regenerate();
            return redirect()->route('dashboard');
        } else {
            return back()->withErrors([
                'gauth_otp' => 'Invalid OTP.',
            ]);
        }
    }

    public function sendOtp(Request $request)
    {
        $rules = [
            'email' => ['required', 'email'],
            'captcha' => 'required|captcha',
        ];
        $messages = [
            'captcha.required' => 'Captcha is required.',
            'captcha.captcha' => 'Please enter a valid captcha.',
        ];
        $validator = Validator::make($request->all(), $rules, $messages);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'validations fails',
                    'errors' => $validator->errors()
                ],
                500
            );
        }
        $user = User::where('email', credential_encrypt($request->email))->first();
        if ($user) {
            $contentData = TemplateModel::where('event', 'Send OTP')->exists()
                ? TemplateModel::where('event', 'Send OTP')->get()
                : TemplateModel::where('event', 'add_email_template')->get();
            // dd($defaultTemplate);

            foreach ($contentData as $contentData) {
                $title = $contentData->title ?? 'O T P Verification Mail';
                $content = $contentData->content ?? 'Please Add Template Content From Template';
                $decodedContent = html_entity_decode($content);

                $plainTextTitle = strip_tags($decodedContent);
                $body = $plainTextTitle ?: 'Default Body';
                $otp = mt_rand(100000, 999999);
                $expiry = now()->addMinutes(10);
                Session::put('otp', $otp);
                $data = $request->json()->all();
                $to_email = $data['email'];

                event(new EmailEvent($to_email, $otp, $expiry, $body, $title));


                EmailActivityLog::create([
                    'email' => $to_email,
                    'subject' => 'OTP Sent',
                    'body' => "Your OTP is " . $otp . " and it expires at " . $expiry,
                    'type' => 'OTP',
                    'status' => 'Email Sent',
                    'sent_at' => now(),
                ]);
                SmsActivityLog::create([
                    'mobile' => '9869856985',
                    // 'message' => "Your OTP is " .$otp. " and it expires at " .$expiry,
                    'message' => "Your OTP is $otp and it expires at $expiry.",
                    // 'body' => 'Your OTP is $otp and it expires at $expiry.',
                    'type' => 'OTP',
                    'status' => 'SMS Sent',
                    'sent_at' => now(),

                ]);

                $user->update([
                    'otp' => $otp,
                    'otp_expiry' => $expiry,
                ]);
                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'OTP Sent to Your Email',
                    ],
                    200
                );
            }
        } else {
            return json_encode([
                'success' => false,
                'message' => config('Login.Error.Message') ?? 'Invalid User',
            ]);
        }
    }
    public function sendEmail(Request $request)
    {
        $user = User::where('username',  credential_encrypt($request->user_name))->Orwhere('email',  credential_encrypt($request->user_name))->Orwhere('mobile',  credential_encrypt($request->user_name))->first();
        if ($user) {

            $contentData = TemplateModel::where('event', 'Reset Password')
            ->orWhere('event', 'add_email_template')
            ->orWhere('event', 'Password Reset')
            ->get();
            // foreach ($contentData as $contentData) {
                $title = count($contentData) ? $contentData->title : 'Password Reset Request';
                $content = count($contentData) ? $contentData->content : '';
                $decodedContent = html_entity_decode($content);
                $plainTextTitle = strip_tags($decodedContent);
                $body = $plainTextTitle ?: 'Default Body';
                $email =  credential_decrypt($user->email);
                $currentDate = Carbon::now();
                $date = $currentDate->addDay();
                $validity = $date;
                $token = $email . '|' . $validity;
                $token = base64_encode($token);
                $url = config('Local.Frontend.Url') . ('/set-new-password') . '?' . http_build_query(['token' => $token]);
                event(new forgotpasswordEvent($email, $url, $body, $title));
                EmailActivityLog::create([
                    'email' => credential_decrypt($user->email),
                    'subject' => 'Reset Password Link Sent',
                    'body' => 'Reset Password Link Sent Succefully to Register Email ID.',
                    'type' => 'Reset Password',
                    'status' => 'Email Sent',
                    'sent_at' => now(),
                ]);
                SmsActivityLog::create([
                    'mobile' => '8964757586',
                    'message' => 'Reset Password Link Sent Succefully to Register Email ID.',
                    'type' => 'Reset Password',
                    'status' => 'SMS Sent',
                    'sent_at' => now(),
                ]);
                
                return response()->json(
                    [
                        'status' => true,
                        'return_data' => [],
                        'message' => 'Reset Password Link Sent Succefully.',
                    ],
                    200
                );
            // }
        } else {
            return response()->json(
                [
                    'status' => false,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'Invalid User',
                ],
                500
            );
        }
    }
    public function otpVerifyPage(Request $request)
    {
        $broker = Broker::select('broker_name')->first();
        $broker_name = $broker->broker_name;

        $email = $request->email;
        return view('auth.loginwithotp ', compact('email', 'broker_name'));
    }
    public function resendOtp(Request $request)
    {
        $user = User::where('email', $request->email)->first();

        $otpMaster = OtpMaster::select('resend_otp_time')->first();
        if (!$otpMaster) {
            return response()->json([
                'success' => false,
                'message' => config('Login.Error.Message') ?? 'Resend OTP time setting not found.',
            ], 500);
        }

        $resendOtpTime = $otpMaster->resend_otp_time;

        if (!$user) {
            return response()->json([
                'success' => false,
                'message' => 'User not found.',
            ]);
        }

        $otp = mt_rand(100000, 999999);
        $expiry = now()->addMinutes($resendOtpTime);

        $user->otp = $otp;
        $user->otp_expiry = $expiry;
        $user->save();

        Mail::to($user->email)->send(new OTPVerificationMail($otp, $expiry));
        EmailActivityLog::create([
            'email' => $request->email,
            'subject' => 'OTP Resent',
            'body' => "Your OTP is " . $otp . " and it expires at " . $expiry,
            'type' => 'OTP Resent',
            'status' => 'Email Sent',
            'sent_at' => now(),
        ]);
        SmsActivityLog::create([
            'mobile' => '7964757599',
            'message' => "Your OTP is " . $otp . " and it expires at " . $expiry,
            // 'body' => 'Your OTP is $otp and it expires at $expiry.',
            'type' => 'OTP Resent',
            'status' => 'SMS Sent',
            'sent_at' => now(),

        ]);

        return response()->json([
            'success' => true,
            'message' => config('Login.Error.Message') ?? 'OTP resent to your email.',
        ]);
    }


    public function forgetPassword(Request $request)
    {
        $token = $request->query('token');
        $decoded_token = credential_decrypt($token);
        $token_parts = explode('|', $decoded_token);
        $email = $token_parts[0];
        $validity = $token_parts[1];
        $currentDate = Carbon::now()->timestamp;
        $user = User::where('email', $email)->first();
        if ($user->email === $email && ($currentDate <= $validity)) {
            $user_id = $user->id;
            return view('user.resetpassword', compact('user_id'));
        } else {
            return redirect()->back()->withErrors(['Link Expired.']);
        }
    }
    public function CustomerSaveResetPassword(Request $request)
    {
        $type = 'password';
        $request->merge(['type' => $type]);
        $rules = [
            'password' => [
                'required',
                'string',
                'min:8',
                'regex:/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/'
            ],
            'confirm_password' => 'required|string|same:password',
        ];
        $messages = [
            'password.required' => 'The password field is required.',
            'password.min' => 'The password must be at least 8 characters.',
            'password.regex' => 'The password must contain at least one uppercase letter, one lowercase letter, one number, and one special character.',
            'confirm_password.required' => 'The confirm password field is required.',
            'confirm_password.same' => 'The confirm password and password must match.',
        ];
        $validator = Validator::make($request->all(), $rules, $messages);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'Validation fails',
                    'errors' => $validator->errors()
                ],
                500
            );
        } else {
            $user = Auth::user();
            if($user){
                if(Hash::check($request->password, $user->password)){
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => config('Login.Error.Message') ?? 'Current password and new password cannot be same.',
                        ],
                        500
                    );
                }else{
                    SaveLoginHistory($user, $request);

                    $login = LoginHistory::where('user_id', $user->id)->first();
                if (empty($login)) {
                    $user->password = Hash::make($request->password);
                } else {
                    $user->password = Hash::make($request->password);
                }
                if ($user->save()) {
                    return response()->json(
                        [
                            'status' => 200,
                            'return_data' => [],
                            'message' => 'Password reset successfully.',
                        ],
                        200
                    );
                } else {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => config('Login.Error.Message') ?? 'Something went wrong.',
                        ],
                        500
                    );
                }
            }
                }


        }
    }

    public function SaveResetPassword(Request $request)
    {
        $rules = [
            'password' => [
                'required',
                'string',
                'min:8',
                'regex:/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/'
            ],
            'confirm_password' => 'required|string|same:password',
        ];
        $messages = [
            'password.required' => 'The password field is required.',
            'password.min' => 'The password must be at least 8 characters.',
            'password.regex' => 'The password must contain at least one uppercase letter, one lowercase letter, one number, and one special character.',
            'confirm_password.required' => 'The confirm password field is required.',
            'confirm_password.same' => 'The confirm password and password must match.',
        ];
        $validator = Validator::make($request->all(), $rules, $messages);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'Validation fails',
                    'errors' => $validator->errors()
                ],
                500
            );
        } else {
            $user = User::where('id', $request->user_id)->first();
            if($user){
                if(Hash::check($request->password, $user->password)){
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => config('Login.Error.Message') ?? 'Current password and new password cannot be same.',
                        ],
                        500
                    );
                }else{
                    $login = LoginHistory::where('user_id', $user->id)->first();
                if (empty($login)) {
                    SaveLoginHistory($user, $request);
                    $user->password = Hash::make($request->password);
                } else {
                    $user->password = Hash::make($request->password);
                }
                if ($user->save()) {
                    return response()->json(
                        [
                            'status' => 200,
                            'return_data' => [],
                            'message' => 'Password reset successfully.',
                        ],
                        200
                    );
                } else {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => config('Login.Error.Message') ?? 'Something went wrong.',
                        ],
                        500
                    );
                }
            }

        }

        }
    }

    public static function ListallUser(Request $request)
    {
        $user = Auth::user();
        $roleId = $user->roles->pluck('id')->first();
        $userAccess = UserAccessManagment::where('role_id', $roleId)->first();
        $allQualification = QualificationMaster::select('qualification_master_id as id','qualification_name as name')->get();
        $decryptedUsers = [];
        if ($userAccess && isset($userAccess->data)) {
            $userAccessData = json_decode($userAccess->data, true);

            if (isset($userAccessData['manage_access'])) {
                foreach ($userAccessData['manage_access'] as $key => $value) {
                    $identifier = $value['identifier'];
                    $usertypeIds = userTypes::whereIn('identifier', (array)$identifier)->pluck('id')->toArray();
                    $users = User::whereIn('usertype', $usertypeIds)->get();

                    foreach ($users as $user) {
                        foreach($allQualification as $qualification){
                            if($user['qualification'] == $qualification['id']){
                                $qualificationData = $qualification;
                                break;
                            }
                            else
                            {
                                $qualificationData = null;
                            }
                        }

                        $decryptedUser = [
                            'id' => $user->id,
                            'name' => credential_decrypt($user->name),
                            'middle_name' => credential_decrypt($user->middle_name),
                            'last_name' => credential_decrypt($user->last_name),
                            'dob' => credential_decrypt($user->dob),
                            'email' => credential_decrypt($user->email),
                            'username' => credential_decrypt($user->username),
                            'mobile' => credential_decrypt($user->mobile),
                            'address' => credential_decrypt($user->address),
                            'pincode' => credential_decrypt($user->pincode),
                            'usertype' => $user->usertype,
                            'is_b2cflag' => $user->is_b2cflag,
                            'data_flag' => $user->data_flag,
                            'reportingto' => $user->reportingto,
                            'employee_code' => $user->employee_code,
                            'gender' => $user->gender,
                            'otp_expires_in' => $user->otp_expires_in,
                            'otp_expires_at' => $user->otp_expires_at,
                            'totp_secret' => credential_decrypt($user->totp_secret),
                            'status' => $user->status,
                            'otp_expiry' => $user->otp_expiry,
                            'license_start_date' => credential_decrypt($user->license_start_date),
                            'license_end_date' => credential_decrypt($user->license_end_date),
                            'email_verified_at' => $user->email_verified_at,
                            // 'password' => $user->password,
                            // 'remember_token' => $user->remember_token,
                            'created_at' => $user->created_at,
                            'updated_at' => $user->updated_at,
                            'deleted_at' => $user->deleted_at,
                            'otp' => $user->otp,
                            'bank_branch' => credential_decrypt($user->bank_branch),
                            'bank_city' => credential_decrypt($user->bank_city),
                            'bank_name' => credential_decrypt($user->bank_name),
                            'account_no' => credential_decrypt($user->account_no),
                            'ifsc_code' => credential_decrypt($user->ifsc_code),
                            'account_holder_name' => credential_decrypt($user->account_holder_name),
                            'nominee_first_name' => $user->nominee_first_name,
                            'nominee_last_name' => $user->nominee_last_name,
                            'nominee_middle_name' => $user->nominee_middle_name,
                            'nominee_relation' => $user->nominee_relation,
                            'nominee_dob' => $user->nominee_dob,
                            'nominee_mobile' => $user->nominee_mobile,
                            'nominee_email' => $user->nominee_email,
                            'zone_id' => $user->zone_id,
                            'Is_delegate' => $user->Is_delegate,
                            'delegate_count' => $user->delegate_count,
                            'pos_code' => $user->pos_code,
                            // 'zoneId' => [
                            //     'id' => $user['zone_id'],
                            //     'office_zone' => ZoneMasterModel::where('id',$user['zone_id'])->pluck('office_zone')[0] ?? ''
                            // ],
                            // 'role' => [
                            //     'id' => $user['role_id'],
                            //     'name' => $user['role_name']
                            // ],
                            'adhar_no' => credential_decrypt($user['adhar_no']),
                            'pan_no' => credential_decrypt($user['pan_no']),
                            'qualification' => $qualificationData,
                            'Status' => $user['status'] == 'Y' ? 'Active' : 'Inactive',
                            'profile_image' => $user->profile_image,
                        ];
                        $decryptedUsers[] = $decryptedUser;
                    }
                }
            }
            return response()->json([
                'status' => true,
                'data' => $decryptedUsers
            ]);
        }else{
            $inactiveResponse = checkUserActivity($request);
            $userIdData = [];
            $userTypeData  = [];
            $user = Auth::user();
            $userroleid = DB::table('model_has_roles')->where('model_id', $user->id)->pluck('role_id');
            $user->role_id = $userroleid[0];
            $roleId = RoleHierarchy($user->role_id, $user->usertype);
            $getUsersOnRoleId = DB::table('model_has_roles')->whereIn('role_id', $roleId)->pluck('model_id')->toArray() ?? [];
            if ($inactiveResponse) {
                return $inactiveResponse;
            }
            $users = User::select('users.id', 'users.name','users.middle_name','users.last_name','users.dob','users.license_start_date','users.license_end_date', 'users.email', 'users.address', 'users.pincode', 'users.gender', 'users.usertype', 'users.mobile', 'users.username','users.reportingto','users.bank_branch','users.bank_name','users.bank_city','users.account_no','users.ifsc_code','users.account_holder_name','users.employee_code','users.pos_code','users.adhar_no','users.pan_no','users.zone_id','users.reportingto as parent_id', 'parent.username as parent_username','parent.name as parent_name','users.status','users.qualification','users.profile_image')->leftJoin('users as parent', 'users.reportingto', '=', 'parent.id');
            $userlob = [];
            if($request->has('id'))
            {
                $users = $users->where('users.id',$request->id);

            }
            else
            {
                if ($request->has('roleName'))
                {
                    $users = $users->join('model_has_roles', 'users.id', '=', 'model_has_roles.model_id')->join('roles', 'roles.id', '=', 'model_has_roles.role_id')->where('roles.name', $request->roleName);
                }
                $usertype = $request->usertype;
                if (!empty($usertype))
                {
                    $users = $users->where('users.usertype', $usertype);
                }
                if (empty($request->roleName) && empty($request->usertype) && empty($request->id))
                {
                    $user = Auth::user();
                    $userId = $user['id'] ?? '';

                    $userType = $user['usertype'] ?? '';
                    $employeeData = userHierarchy($userId, $userType);
                    if (!isset($employeeData['isAdmin'])) {
                        foreach ($employeeData as $key => $value) {
                            $userIdData[] = $value['id'];
                            $userTypeData[] = $value['usertype'];
                        }
                        $userTypeData = array_unique($userTypeData);
                        $result = array_merge($userIdData,$getUsersOnRoleId);
                        $users = $users->whereIn('users.id', $result)->where('users.usertype', $userTypeData);
                    }
                    if (!empty($users))
                    {
                        foreach ($users as $key => $value)
                        {
                            if ($value->id == $user['id'])
                            {
                                unset($users[$key]);
                            }
                        }
                    }
                }
                else
                {
                    $users = $users->whereIn('users.id', $getUsersOnRoleId);
                }
            }
            if($request->has('search'))
            {
                $search = credential_encrypt($request->search);
                $users = $users->Where( function($query) use($search){
                    $query->orWhere('users.name', 'like', '%' .$search . '%')
                    ->orWhere('users.email', 'like', '%' .$search . '%')
                    ->orWhere('users.mobile', 'like', '%' .$search . '%')
                    ->orWhere('users.username', 'like', '%' .$search . '%')
                    ->orWhere('users.middle_name', 'like', '%' .$search . '%')
                    ->orWhere('users.last_name', 'like', '%' .$search . '%');
                });
            }
            $users = $users->where('users.username', '!=', credential_encrypt('super_admin'));
            if($request->has('paginate') && $request->paginate == 'true')
            {
                $ShowCount = $request->show ?? 10;
                $users = $users->paginate($ShowCount);
                $lastPage = $users->lastPage();
                $totalCount = $users->total();
            }
            else
            {
                $users = $users->get();
            }


                $rolesDetails  = Role::select('id','name')->get();
                foreach ($users as $uk => $u) {
                    $roles = $u->getRoleNames()->toArray();
                    if (empty($roles)) {
                        unset($users[$uk]);
                    } else {
                        $users[$uk]['Userroles'] = $roles[0];
                        unset($users[$uk]['roles']);
                    }
                }
            if($request->has('paginate') && $request->paginate == 'true')
            {
                $users = $users->toArray()['data'];
            }
            else
            {
                $users = $users->toArray();
            }
                $usersData = [];
                $userlob = SellNow::select('user_lob_relation.lob_id as id','lob_master.lob as name','user_lob_relation.user_id')->join('lob_master', 'lob_master.id', '=', 'user_lob_relation.lob_id')->get()->toArray();
                $usertypedata = userTypes::select('id', 'name', 'Identifier')->get();
                $roportingtoUserDetails = User::select('id','name')->get()?? '';
                $zoneData = ZoneMasterModel::select('id','office_zone')->get();
                $reportingUserRole =  DB::table('model_has_roles')->join('roles', 'roles.id', '=', 'model_has_roles.role_id')->select('roles.name','roles.id','model_has_roles.model_id')->get();

                foreach ($users as $user)
                {
                    foreach($allQualification as $qualification){
                        if($user['qualification'] == $qualification['id'])
                        {
                            $qualificationData = $qualification;
                            break;
                        }
                        else
                        {
                            $qualificationData = null;
                        }
                    }
                    foreach ($rolesDetails as $key => $value) {
                        if(isset($user['Userroles']) && $value['name'] == $user['Userroles'])
                        {
                            $user['role_id'] = $value['id'];
                            $user['role_name'] = $value['name'];
                        }
                    }
                    $roportingtoUserDetailsres  = $reportingUserRoleres = $usertypedatares = null;
                    $userlobres = [];
                    foreach ($userlob as $key => $value) {
                        if($value['user_id'] == $user['id'])
                        {
                            $userlobres[] = $value;
                        }
                        else
                        {
                            continue;
                        }
                    }
                    foreach ($roportingtoUserDetails as $key => $value) {
                        if($value['id'] == $user['reportingto'])
                        {
                            $roportingtoUserDetailsres = $value;
                            break;
                        }
                    }
                    $reportingData = [];
                    foreach ($reportingUserRole as $key => $value) {
                        if($value->model_id == $user['reportingto'])
                        {
                            $reportingUserRoleres = $value;
                            break;
                        }
                    }
                    if( isset($roportingtoUserDetailsres))
                    {
                        $reportingData['id'] = $roportingtoUserDetailsres['id'];
                        $reportingData['name'] = credential_decrypt($roportingtoUserDetailsres['name']);
                    }
                    foreach ($usertypedata as $key => $value) {
                        if($value['id'] == $user['usertype'])
                        {
                            $usertypedatares = $value;
                            break;
                        }
                    }

                    if ($usertypedatares) {
                        $usertypeName = $usertypedatares['name'];
                        $usertypeIdentifier = $usertypedatares['Identifier'];
                    } else
                    {
                        // Handle the case when no user type is found
                        $usertypeName = null;
                        $usertypeIdentifier = null;
                    }
                    $zoneDatares = '';
                    foreach ($zoneData as $key => $value) {
                        if($value['id'] == $user['zone_id'])
                        {
                            $zoneDatares = $value['office_zone'];
                            break;
                        }
                    }

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
                        'dob' => credential_decrypt($user['dob']) ?? '',
                        'license_start_date' => credential_decrypt($user['license_start_date']) ?? '',
                        'license_end_date' => credential_decrypt($user['license_end_date']) ?? '',
                        'zoneId' => [
                            'id' => $user['zone_id'],
                            'office_zone' => $zoneDatares
                        ],
                        'reportingTo' =>  $reportingData ?? '',
                        'reportingRole' => $reportingUserRoleres,
                        'usertype' => [
                            'id' => $user['usertype'],
                            'name' => $usertypeName ?? '',
                            'Identifier' => $usertypeIdentifier ?? ''
                        ],
                        'lob_id' => $userlobres,
                        'role' => [
                            'id' => $user['role_id'] ?? '',
                            'name' => $user['role_name'] ?? ''
                        ],
                        'adhar_no' => credential_decrypt($user['adhar_no']),
                        'pan_no' => credential_decrypt($user['pan_no']),
                        'qualification' => $qualificationData,
                        'Status' => $user['status'] == 'Y' ? 'Active' : 'Inactive',
                        'profile_image' => $user['profile_image'] 
                        ? Storage::disk('public')->url($user['profile_image']) 
                        : null,
                    ];
                }

            return response()->json([
                'status' => "true",
                'data' => $usersData,
                'total' => $totalCount ?? '',
                'LastPage' => $lastPage ?? ''
            ]);
        }

    }
    public static function getUserList(Request $request)
    {
        $user = Auth::user();
        $roleId = $user->roles->pluck('id')->first();
         $userAccess = UserAccessManagment::where('role_id', $roleId)->first();
        $allQualification = QualificationMaster::select('qualification_master_id as id','qualification_name as name')->get();
        $decryptedUsers = [];
         if (false) {       // putting it false because i dont dont want it to go in this block, we want this to go in else block
            $userAccessData = json_decode($userAccess->data, true);

            if (isset($userAccessData['manage_access'])) {
                foreach ($userAccessData['manage_access'] as $key => $value) {
                    $identifier = $value['identifier'];
                    $usertypeIds = userTypes::whereIn('identifier', (array)$identifier)->pluck('id')->toArray();

                    $users = User::select(
                        'users.id',
                        'users.name',
                        'users.middle_name',
                        'users.last_name',
                        'users.dob',
                        'users.license_start_date',
                        'users.license_end_date',
                        'users.email',
                        'users.address',
                        'users.pincode',
                        'users.gender',
                        'users.usertype',
                        'users.mobile',
                        'users.username',
                        'users.reportingto',
                        'users.bank_branch',
                        'users.bank_name',
                        'users.bank_city',
                        'users.account_no',
                        'users.ifsc_code',
                        'users.account_holder_name',
                        'users.employee_code',
                        'users.pos_code',
                        'users.adhar_no',
                        'users.pan_no',
                        'users.zone_id',
                        'users.reportingto as parent_id',
                        'parent.username as parent_username',
                        'parent.name as parent_name',
                        'users.status',
                        'users.qualification',
                        'users.profile_image'
                    )
                    ->leftJoin('users as parent', 'users.reportingto', '=', 'parent.id')
                    ->whereIn('users.usertype', $usertypeIds); // Explicitly reference the `users` table

                    if($request->has('usertype'))
                    {
                        $users->where('users.usertype',$request->usertype);
                    }

                    if($request->has('id'))
                    {
                        $users->where('users.id',$request->id);
                    }
                    

                    $users = $users->get();

                    $rolesDetails  = Role::select('id','name')->get();
                    foreach ($users as $uk => $u) {
                        $roles = $u->getRoleNames()->toArray();
                        if (empty($roles)) {
                        } else {
                            $users[$uk]['Userroles'] = $roles[0];
                        }
                    }
                    $index = 0;
                    foreach ($users as $user) {
                        $index++;
                        foreach($allQualification as $qualification){
                            if($user['qualification'] == $qualification['id']){
                                $qualificationData = $qualification;
                                break;
                            }
                            else
                            {
                                $qualificationData = null;
                            }

                            foreach ($rolesDetails as $key => $value) {
                                if(isset($user['Userroles']) && $value['name'] == $user['Userroles'])
                                {
                                    $user['role_id'] = $value['id'];
                                    $user['role_name'] = $value['name'];
                                }
                            }
                            $roportingtoUserDetailsres  = $reportingUserRoleres = $usertypedatares = null;

                        }

                        $userlobData = SellNow::select('lob_id')->where('user_id', $user->id)->get();
                        $lobIdArray = $userlobData->pluck('lob_id');
        
        
                        $lobName = lobMaster::whereIn('id', $lobIdArray)->select('id', 'lob')->get();

                        $decryptedUser = [
                            'sr_no' => $index,
                            'id' => $user->id,
                            'name' => credential_decrypt($user->name),
                            'middle_name' => credential_decrypt($user->middle_name),
                            'last_name' => credential_decrypt($user->last_name),
                            'dob' => credential_decrypt($user->dob),
                            'license_start_date' => credential_decrypt($user->license_start_date),
                            'license_end_date' => credential_decrypt($user->license_end_date),
                            'email' => credential_decrypt($user->email),
                            'email_verified_at' => $user->email_verified_at,
                            'password' => $user->password,
                            'remember_token' => $user->remember_token,
                            'created_at' => $user->created_at,
                            'updated_at' => $user->updated_at,
                            'deleted_at' => $user->deleted_at,
                            'otp' => $user->otp,
                            'username' => credential_decrypt($user->username),
                            'mobile' => credential_decrypt($user->mobile),
                            'parent_username' => credential_decrypt($user['parent_username']),
                            'parent_name' => credential_decrypt($user['parent_name']),
                            'address' => credential_decrypt($user->address),
                            'pincode' => credential_decrypt($user->pincode),
                            'gender' => $user->gender,
                            'otp_expires_in' => $user->otp_expires_in,
                            'otp_expires_at' => $user->otp_expires_at,
                            'totp_secret' => credential_decrypt($user->totp_secret),
                            'status' => $user->status,
                            'otp_expiry' => $user->otp_expiry,
                            'usertype' => $user->usertype,
                            'bank_branch' => credential_decrypt($user->bank_branch),
                            'bank_city' => credential_decrypt($user->bank_city),
                            'bank_name' => credential_decrypt($user->bank_name),
                            'account_no' => credential_decrypt($user->account_no),
                            'ifsc_code' => credential_decrypt($user->ifsc_code),
                            'account_holder_name' => credential_decrypt($user->account_holder_name),
                            'nominee_first_name' => $user->nominee_first_name,
                            'nominee_last_name' => $user->nominee_last_name,
                            'nominee_middle_name' => $user->nominee_middle_name,
                            'nominee_relation' => $user->nominee_relation,
                            'nominee_dob' => $user->nominee_dob,
                            'nominee_mobile' => $user->nominee_mobile,
                            'nominee_email' => $user->nominee_email,
                            'reportingto' => $user->reportingto,
                            'employee_code' => $user->employee_code,
                            'zone_id' => $user->zone_id,
                            'Is_delegate' => $user->Is_delegate,
                            'delegate_count' => $user->delegate_count,
                            'pos_code' => $user->pos_code,
                            'zoneId' => [
                                'id' => $user['zone_id'],
                                'office_zone' => ZoneMasterModel::where('id',$user['zone_id'])->pluck('office_zone')[0] ?? ''
                            ],
                            'role' => [
                                'id' => $user['role_id'],
                                'name' => $user['role_name']
                            ],
                            'lob_id' => $lobName ?? null,   
                            'adhar_no' => credential_decrypt($user['adhar_no']),
                            'pan_no' => credential_decrypt($user['pan_no']),
                            'qualification' => $qualificationData,
                            'Status' => $user['status'] == 'Y' ? 'Active' : 'Inactive',
                            'profile_image' => $user->profile_image,
                        ];
                        $decryptedUsers[] = $decryptedUser;
                    }
                }
            }

            $totalItems = count($decryptedUsers);
            $paginatedCollection = collect($decryptedUsers);
            $currentPage = $request->page ?? 1;
            $perPage = 10;

            $paginatedData = $paginatedCollection->forPage($currentPage, $perPage);
            $paginatedArray = $paginatedData->values()->all();
            $lastPage = (int) ceil($totalItems / $perPage); 
        
            return response()->json([
                'status' => true,
                'data' => $paginatedArray,
                'total' => $totalItems,
                'LastPage' => $lastPage
            ]);
        }else{
   
            $inactiveResponse = checkUserActivity($request);
            if ($inactiveResponse) {
                return $inactiveResponse;
            }
            $userIdData = [];
            $userTypeData  = [];
            $userroleid = $roleId;
            $getUserHierarchyData = getUserLowerHierarchy($user->id,$user->userType->id);

             if (empty($getUserHierarchyData) && $user->userType->id !=1) {
                return response()->json([
                    'status' => false,
                    'data' => []
                ]);
            }

            $getuserType = userTypes::select('id','name','Identifier')->where('is_active', 'Y')->get()->toArray();
            $getUsertypeIdentifier = '';

            foreach($getuserType as $value){
                if($value['id'] ==  $user->usertype){
                    
                    $getUsertypeIdentifier = $value['Identifier'];
                }
            }

 
            $UserHierarchyArray = [];
            $UserHierarchyEmpCode = [];
            $idsToFilter = [];

                foreach($getUserHierarchyData as $value){
                    $UserHierarchyArray[] =$value['id'];
                    $UserHierarchyEmpCode[] =$value['employee_code'];
                }
                $UserHierarchyEmpCode[] =$user->employee_code;

                $finalMappingData = [];
                if(!$request->has('mode'))
                {
                    if($getUsertypeIdentifier == 'E' && $user->is_admin == 'N'){
                        $finalMappingData = getMapPosPartner($UserHierarchyEmpCode);
                        $finalMappingData = array_filter($finalMappingData, fn($item) => $item['id'] !== $user->id);
                    }
                 
                }

             
            $users = User::select('users.id', 'users.name','users.middle_name','users.last_name','users.dob','users.license_start_date','users.license_end_date', 'users.email', 'users.address', 'users.pincode', 'users.gender', 'users.usertype', 'users.mobile', 'users.username','users.reportingto','users.bank_branch','users.bank_name','users.bank_city','users.account_no','users.ifsc_code','users.account_holder_name','users.employee_code','users.pos_code','users.adhar_no','users.pan_no','users.oemId','users.mispId','users.branchId','users.zone_id','users.reportingto as parent_id', 'parent.username as parent_username','parent.name as parent_name','users.status','users.qualification','users.profile_image')->leftJoin('users as parent', 'users.reportingto', '=', 'parent.id');
            $userlob = [];

            
            if($request->has('id'))
            {
                $users = $users->where('users.id',$request->id);
            }


            if ($request->has('roleName')) {

                $users = $users->join('model_has_roles', 'users.id', '=', 'model_has_roles.model_id')->join('roles', 'roles.id', '=', 'model_has_roles.role_id')->where('roles.name', $request->roleName);
            }
    
            if (!$request->has('mode')) {

                if($user->usertype == 1){
                  // Check if the collections/arrays are not empty
                    if (!empty($finalMappingData) || !empty($UserHierarchyArray)) {
                        // Combine arrays for filtering if both exist

                        // Step 1: Extract 'id' from the first array
                        $finalMappingDataArray = array_column($finalMappingData, 'id');

                        $idsToFilter = array_unique(array_merge(
                            $finalMappingDataArray ?? [],
                            $UserHierarchyArray ?? []
                        ));


                    }

                    if($user->is_admin == 'Y'){
                         $users->pluck('users.id');
                        // $users->whereIn('users.is_admin',['Y','N']);
         
                    }else{
                        $users->whereIn('users.id', $idsToFilter);
                    }


                }else{
                    
                        $users->whereIn('users.id', $UserHierarchyArray);
                    
                }


            }  
            if($request->has('usertype'))
            {
                $users->where('users.usertype',$request->usertype);
            }
            
            if($request->has('search') && !empty($request->search))
            {
                $search = credential_encrypt($request->search);
                $users = $users->Where( function($query) use($search){
                    $query->orWhere('users.name', 'like', '%' .$search . '%')
                    ->orWhere('users.email', 'like', '%' .$search . '%')
                    ->orWhere('users.mobile', 'like', '%' .$search . '%')
                    ->orWhere('users.username', 'like', '%' .$search . '%')
                    ->orWhere('users.middle_name', 'like', '%' .$search . '%')
                    ->orWhere('users.last_name', 'like', '%' .$search . '%');
                });
            }
            $users = $users->where('users.username', '!=', credential_encrypt('super_admin'));
            if($request->has('mode') && $request->mode == 'nonDelegateUsers')
            {
                $users = $users->where('users.Is_delegate', 'N');
            }
            $isAdmin  = UserIsAdmin($user->id);
            if($isAdmin)
            {
                // $users = $users->select('*');
            }
            if($request->has('paginate') && $request->paginate == 'true')
            {
                 $ShowCount = $request->show ?? 10;
                $users = $users->paginate($ShowCount);
                $lastPage = $users->lastPage();
                $totalCount = $users->total();
            }
            else
            {
 
                $users = $users->get();
            }
 
                $rolesDetails  = Role::select('id','name')->get();
                foreach ($users as $uk => $u) {
                    $roles = $u->getRoleNames()->toArray();
                    if (empty($roles)) {
                        // unset($users[$uk]);
                    } else {
                        $users[$uk]['Userroles'] = $roles[0];
                        // unset($users[$uk]['roles']);
                    }
                }
    
                $usersData = [];
                $userlob = SellNow::select('user_lob_relation.lob_id as id','lob_master.lob as name','user_lob_relation.user_id')->join('lob_master', 'lob_master.id', '=', 'user_lob_relation.lob_id')->get()->toArray();
                $usertypedata = userTypes::select('id', 'name', 'Identifier')->get();
                $roportingtoUserDetails = User::select('id','name')->get()?? '';
                $zoneData = ZoneMasterModel::select('id','office_zone')->get();
                $reportingUserRole =  DB::table('model_has_roles')->join('roles', 'roles.id', '=', 'model_has_roles.role_id')->select('roles.name','roles.id','model_has_roles.model_id')->get();

                $mappedEmployeeForPos = [];
                
                $index = 0;
                foreach ($users as $user)
                {

                    if($user->usertype == 2){
                        $empcodeofparticularpos = $user->employee_code ?? null;
                        $mappedEmployee = User::select('id', 'name')->where('employee_code',$empcodeofparticularpos)->where('usertype', 1)->orderBy('id', 'asc')->first() ?? null;

                        if ($mappedEmployee) {
                            $mappedEmployeeForPos = [
                                'id' => $mappedEmployee->id,
                                'name' => credential_decrypt($mappedEmployee->name),
                            ];
                        }
                        
                    }
                    
                    if($user->usertype == 6){

                        $mispData = User::join('oem_master_data', 'oem_master_data.oem_id', '=', 'users.oemId')->join('misp_masters','misp_masters.oem_id','=','oem_master_data.oem_id')->join('misp_branches','misp_branches.branch_id','=','misp_masters.misp_id')->select('oem_master_data.oem_id','oem_master_data.oem_name','misp_branches.branch_id','misp_branches.branch_name','misp_masters.misp_id','misp_masters.misp_name')->get();
                      
                        $oemData = [];
                        $mispDropdownData = [];
                        $branchData = [];

                        foreach($mispData as $misp){
                            $oemData = [
                                'id' => $misp->oem_id,
                                'name' => $misp->oem_name,
                            ];
                            $mispDropdownData = [
                                'id' => $misp->misp_id,
                                'name' => $misp->misp_name,
                            ];
                            $branchData = [
                                'id' => $misp->branch_id,
                                'name' => $misp->branch_name,
                            ];
                        }
            
                    }

                    $index++;
                    foreach($allQualification as $qualification){
                        if($user['qualification'] == $qualification['id'])
                        {
                            $qualificationData = $qualification;
                            break;
                        }
                        else
                        {
                            $qualificationData = null;
                        }
                    }
                    foreach ($rolesDetails as $key => $value) {
                        if(isset($user['Userroles']) && $value['name'] == $user['Userroles'])
                        {
                            $user['role_id'] = $value['id'];
                            $user['role_name'] = $value['name'];
                        }
                    }
                    $roportingtoUserDetailsres  = $reportingUserRoleres = $usertypedatares = null;
                    $userlobres = [];
                    foreach ($userlob as $key => $value) {
                        if($value['user_id'] == $user['id'])
                        {
                            $userlobres[] = $value;
                        }
                        else
                        {
                            continue;
                        }
                    }
                    foreach ($roportingtoUserDetails as $key => $value) {
                        if($value['id'] == $user['reportingto'])
                        {
                            $roportingtoUserDetailsres = $value;
                            break;
                        }
                    }
                    $reportingData = [];
                    foreach ($reportingUserRole as $key => $value) {
                        if($value->model_id == $user['reportingto'])
                        {
                            $reportingUserRoleres = $value;
                            break;
                        }
                    }
                    if( isset($roportingtoUserDetailsres))
                    {
                        $reportingData['id'] = $roportingtoUserDetailsres['id'];
                        $reportingData['name'] = credential_decrypt($roportingtoUserDetailsres['name']);
                    }
                    foreach ($usertypedata as $key => $value) {
                        if($value['id'] == $user['usertype'])
                        {
                            $usertypedatares = $value;
                            break;
                        }
                    }

                    if ($usertypedatares) {
                        $usertypeName = $usertypedatares['name'];
                        $usertypeIdentifier = $usertypedatares['Identifier'];
                    } else
                    {
                        // Handle the case when no user type is found
                        $usertypeName = null;
                        $usertypeIdentifier = null;
                    }
                    $zoneDatares = '';
                    foreach ($zoneData as $key => $value) {
                        if($value['id'] == $user['zone_id'])
                        {
                            $zoneDatares = $value['office_zone'];
                            break;
                        }
                    }

                    $usersData[] = [
                        'sr_no' => $index,
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
                        'dob' => credential_decrypt($user['dob']) ?? '',
                        'license_start_date' => credential_decrypt($user['license_start_date']) ?? '',
                        'license_end_date' => credential_decrypt($user['license_end_date']) ?? '',
                        'posCode' => $user['pos_code'] ?? null,
                        'zoneId' => [
                            'id' => $user['zone_id'],
                            'office_zone' => $zoneDatares
                        ],
                        'reportingTo' =>  $reportingData ?? '',
                        'reportingRole' => $reportingUserRoleres,
                        'usertype' => [
                            'id' => $user['usertype'],
                            'name' => $usertypeName ?? '',
                            'Identifier' => $usertypeIdentifier ?? ''
                        ],
                        'lob_id' => $userlobres,
                        'role' => [
                            'id' => $user['role_id'] ?? '',
                            'name' => $user['role_name'] ?? ''
                        ],
                        'user_role' => $user['role_name'] ?? null,
                        'oem_list' => $oemData ?? null,
                        'misp_list' => $mispDropdownData ?? null,
                        'branch_list' => $branchData ?? null,
                        'reporting_employee' => $mappedEmployeeForPos ?? null,
                        'adhar_no' => credential_decrypt($user['adhar_no']),
                        'pan_no' => credential_decrypt($user['pan_no']),
                        'qualification' => $qualificationData,
                        'Status' => $user['status'] == 'Y' ? 'Active' : 'Inactive',
                        'profile_image' => $user['profile_image'] 
                        ? Storage::disk('public')->url($user['profile_image']) 
                        : null,
                    ];
                }
                if($request->has('mode') && $request->mode == 'nonDelegateUsers')
                {
                    $newdata = [];
                    foreach ($usersData as $value) {
                        $newdata[] = [
                            'id' => $value['id'],
                            'username' => $value['username'],
                        ];
                    }
                   $usersData = $newdata;
                }

            return response()->json([
                'status' => "true",
                'data' => $usersData,
                'total' => $totalCount ?? '',
                'LastPage' => $lastPage ?? ''
            ]);

        }

    }
    public static function getAllUserList(Request $request)
    {
      
          
        $searchTerm = $request->input('search', '');
        $userType = $request->input('usertype', '');
        $userId = $request->input('id', '');

        $perPage = $request->input('per_page', 10); 
        //with userRoles
        $users = User::with('roles')->when($searchTerm, function ($query, $searchTerm) {
            return $query->where('username', 'like', "%{$searchTerm}%");
        })
        ->when($userType, function ($query, $userType) {
            return $query->where('usertype', $userType);
        })
        ->when($userId, function ($query, $userId) {
            return $query->where('id', $userId);
        })
        ->paginate($perPage);

                foreach ($users as $user) {
                  
                    $decryptedUser = [
                        // 'sr_no' => $index,
                        'id' => $user->id,
                        'username' => credential_decrypt($user->username),
                        'mobile' => credential_decrypt($user->mobile),
                        'usertype' => $user->usertype,
                        'employee_code' => $user->employee_code,
                        'reportingto' => $user->reportingto,
                        'is_admin' => $user->is_admin,
                        'name' => credential_decrypt($user->name),
                        'middle_name' => credential_decrypt($user->middle_name),
                        'last_name' => credential_decrypt($user->last_name),
                        'email' => credential_decrypt($user->email),
                        'dob' => credential_decrypt($user->dob),
                        'license_start_date' => credential_decrypt($user->license_start_date),
                        'license_end_date' => credential_decrypt($user->license_end_date),
                
                        'created_at' => $user->created_at,
                        'deleted_at' => $user->deleted_at,
                        'otp' => $user->otp,
                        // 'parent_username' => credential_decrypt($user['parent_username']),
                        // 'parent_name' => credential_decrypt($user['parent_name']),
                        'address' => credential_decrypt($user->address),
                        'pincode' => credential_decrypt($user->pincode),
                        'gender' => $user->gender,
                        'otp_expires_in' => $user->otp_expires_in,
                        'otp_expires_at' => $user->otp_expires_at,
                        // 'totp_secret' => credential_decrypt($user->totp_secret),
                        'status' => $user->status,
                        'otp_expiry' => $user->otp_expiry,
                        'zone_id' => $user->zone_id,
                        'Is_delegate' => $user->Is_delegate,
                        'delegate_count' => $user->delegate_count,
                        'pos_code' => $user->pos_code,
                      
                       'role' => [
                            'id' => $user->roles->first()->id ?? '',
                            'name' => $user->roles->first()->name ?? ''
                        ],
                        'lob_id' => $lobName ?? null,   
                        'adhar_no' => credential_decrypt($user['adhar_no']),
                        'pan_no' => credential_decrypt($user['pan_no']),
                        // 'qualification' => $qualificationData,
                        'Status' => $user['status'] == 'Y' ? 'Active' : 'Inactive',
                        'old_user_id' => $user->old_user_id ?? null,
                    ];
                    $decryptedUsers[] = $decryptedUser;
                }      
            return response()->json([
                'message' => 'Users fetched successfully.',
                'total' => $users->total(),
                'status' => true,
                'data' => $decryptedUsers
            ]);


    }

    public function getLoginCounts(Request $request)
{
        $auth = Auth::user();
        $viewPermission = "Login History.view";
        if (!$auth->can($viewPermission)) {
            return response()->json([
                'success' => false,
                'message' => config('Login.Error.Message') ?? 'You do not have permission to access this resource.',
            ], 403);
        }
    $inactiveResponse = checkUserActivity($request);
    if ($inactiveResponse) {
        return $inactiveResponse;
    }

    $validated = $request->validate([
        'start_date' => 'required|date_format:d/m/Y',
        'end_date' => 'required|date_format:d/m/Y|after_or_equal:start_date',
        'user_id' => 'nullable|integer',
    ]);

    $startDate = Carbon::createFromFormat('d/m/Y', $request->start_date)->startOfDay();
    $endDate = Carbon::createFromFormat('d/m/Y', $request->end_date)->endOfDay();

    $authUserId = Auth::id();
    $isAdminAuthUser = UserIsAdmin($authUserId);

    $userIdToQuery = $request->filled('user_id') ? $request->user_id : $authUserId;
    $isRequestedUserAdmin = UserIsAdmin($userIdToQuery);

    if ($request->filled('user_id')) {
        if ($isRequestedUserAdmin) {
            $userHierarchy = User::select('id')->get()->toArray();
        } else {
            $userHierarchy = getUserLowerHierarchyForLoginCount($userIdToQuery, Auth::user()->usertype ?? null);
        }
    } else {
        if ($isAdminAuthUser) {
            $userHierarchy = User::select('id')->get()->toArray();
            // $userHierarchy = Customer::select('id')->get()->toArray();
        } else {
            $userHierarchy = getUserLowerHierarchyForLoginCount($authUserId, Auth::user()->usertype ?? null);
        }
    }
    $customers = Customer::select('id')->get()->toArray();

    $userHierarchy = array_merge($userHierarchy, $customers);

    $userIds = array_column($userHierarchy, 'id');

    if (!$request->filled('user_id') && !$isAdminAuthUser) {
        $userIds[] = $authUserId;
    }

    // $loginCountsQuery = LoginHistory::select(
    //     DB::raw('DATE(login_history.created_at) as login_date'),
    //     'users.id as user_id',
    //     'users.usertype',
    //     'usertypes.Identifier as usertype_identifier' // Change to use Identifier
    // )
    // ->leftjoin('users', 'login_history.user_id', '=', 'users.id')
    // ->leftjoin('customers', 'login_history.user_id', '=', 'customers.id')
    // ->join('usertypes', 'users.usertype', '=', 'usertypes.id')
    // ->whereBetween('login_history.created_at', [$startDate, $endDate]);
    DB::enableQueryLog();
    $loginCountsQuery = LoginHistory::select(
        DB::raw('DATE(login_history.created_at) as login_date'),
        DB::raw('COALESCE(users.id, customers.id) as user_id'),
        DB::raw('COALESCE(uu.Identifier, uc.Identifier) as usertype_identifier'),
        'login_history.usertype',
        'login_history.login_history_id'
    )
    ->leftJoin('users', function ($join) {
        $join->on('login_history.user_id', '=', 'users.id')
             ->where('login_history.usertype', '!=', 5);
    })
    ->leftJoin('customers', function ($join) {
        $join->on('login_history.user_id', '=', 'customers.id')
             ->where('login_history.usertype', '=', 5);
    })
    ->leftJoin('usertypes as uu', 'users.usertype', '=', 'uu.id')
    ->leftJoin('usertypes as uc', 'customers.usertype', '=', 'uc.id')
    ->whereBetween('login_history.created_at', [$startDate, $endDate])
    ->whereNotNull('login_history.usertype');

    if (!empty($userIds)) {
        $loginCountsQuery->whereIn('login_history.user_id', $userIds);
    }

    $loginCounts = $loginCountsQuery->get();
    
    $datewiseLoginCounts = $loginCounts->groupBy('login_date')->map(function ($logins) {
        $userTypeCounts = [];

        foreach ($logins as $login) {
            $userTypeIdentifier = $login->usertype_identifier; // Use Identifier for grouping
            $userId = $login->user_id;

            if (!isset($userTypeCounts[$userTypeIdentifier])) {
                $userTypeCounts[$userTypeIdentifier] = [];
            }

            if (!in_array($userId, $userTypeCounts[$userTypeIdentifier])) {
                $userTypeCounts[$userTypeIdentifier][] = $userId;
            }
        }

        $totalLoginCount = array_reduce($userTypeCounts, function ($carry, $userIds) {
            return $carry + count($userIds);
        }, 0);

        return [
            'login_count' => $totalLoginCount,
            'user_counts' => array_map('count', $userTypeCounts),
        ];
    });

    $formattedLoginCounts = [];
    foreach ($datewiseLoginCounts as $date => $counts) {
        $formattedEntry = [
            'login_date' => Carbon::parse($date)->format('d/m/Y'),
            'login_count' => $counts['login_count'],
        ];

        foreach ($counts['user_counts'] as $type => $count) {
            $formattedEntry[$type] = $count;
        }

        $formattedLoginCounts[] = $formattedEntry;
    }

    usort($formattedLoginCounts, function ($a, $b) {
        return Carbon::createFromFormat('d/m/Y', $b['login_date'])->timestamp - Carbon::createFromFormat('d/m/Y', $a['login_date'])->timestamp;
    });

    return response()->json([
        'total_login_count' => $loginCounts->unique('usertype')->count(),
        'key-array' => ['login_date', 'login_count', 'usertype_identifier'],
        'datewise_login_counts' => $formattedLoginCounts,
    ]);
}


    public function userLoginCounts(Request $request)
{
        $user = Auth::user();
        $viewPermission = "Login History.view";
        if (!$user->can($viewPermission)) {
            return response()->json([
                'success' => false,
                'message' => config('Login.Error.Message') ?? 'You do not have permission to access this resource.',
            ], 403);
        }

    $inactiveResponse = checkUserActivity($request);
    if ($inactiveResponse) {
        return $inactiveResponse;
    }

    $user = Auth::user();

    $validated = $request->validate([
        'date' => 'required|date_format:d/m/Y',
        'end_date' => 'sometimes|required|date_format:d/m/Y|after_or_equal:date',
        'type' => 'required|string|in:summary,detailed',
        'user_type' => 'sometimes|nullable|string|exists:usertypes,Identifier', // Validate against Identifier
        'user_id' => 'sometimes|nullable|integer|exists:users,id',
    ]);

    $authUserId = Auth::id();
    $isAdmin = UserIsAdmin($authUserId);

    $userIdToQuery = $request->filled('user_id') ? $request->user_id : $authUserId;

        if ($request->filled('user_id')) {
            $isRequestedUserAdmin = UserIsAdmin($request->user_id);
            $userHierarchy = getUserLowerHierarchyForLoginCount($userIdToQuery,User::find($request->user_id)->usertype);
        } else {
            $userHierarchy = $isAdmin
                ? User::select('id')->get()->toArray()
                : getUserLowerHierarchyForLoginCount($userIdToQuery, Auth::user()->usertype ?? null);
        }

    $userIds = array_column($userHierarchy, 'id');

    $startDate = Carbon::createFromFormat('d/m/Y', $request->date)->startOfDay();
    $endDate = $request->has('end_date')
        ? Carbon::createFromFormat('d/m/Y', $request->end_date)->endOfDay()
        : Carbon::now()->endOfDay();
        $endDate = Carbon::createFromFormat('d/m/Y', $request->date)->endOfDay();


        $loginCountsQuery = LoginHistory::select(
            DB::raw('DATE(login_history.created_at) as login_date'),
            DB::raw('COALESCE(users.id, customers.id) as user_id'),
            DB::raw('COALESCE(uu.Identifier, uc.Identifier) as usertype_identifier'),
            'login_history.usertype',
            'login_history.login_history_id'
        )->select('usertypes.Identifier as user_type', DB::raw('count(*) as login_count'))
        ->leftJoin('users', function ($join) {
            $join->on('login_history.user_id', '=', 'users.id')
                 ->where('login_history.usertype', '!=', 5);
        })
        ->leftJoin('customers', function ($join) {
            $join->on('login_history.user_id', '=', 'customers.id')
                 ->where('login_history.usertype', '=', 5);
        })
        ->leftJoin('usertypes as uu', 'users.usertype', '=', 'uu.id')
        ->leftJoin('usertypes as uc', 'customers.usertype', '=', 'uc.id')
        ->whereBetween('login_history.created_at', [$startDate, $endDate])
        ->whereNotNull('login_history.usertype');

    if ($request->has('user_type') && !empty($request->user_type)) {
        $loginCountsQuery->where(function ($query) use ($request) {
            $query->where('uu.Identifier', $request->user_type)
                  ->orWhere('uc.Identifier', $request->user_type);
        });        
    }

    if ($request->type === 'detailed') {
        if($request->user_type=='U'){
            $loginCountsQuery->addSelect('customers.id', 'customers.name', 'customers.email', 'customers.username');
            $loginCountsQuery->groupBy('uc.Identifier', 'customers.id', 'customers.name', 'customers.email', 'customers.username');
        }else{
            $loginCountsQuery->addSelect('users.id', 'users.name', 'users.email', 'users.username');
            $loginCountsQuery->groupBy('usertypes.Identifier', 'users.id', 'users.name', 'users.email', 'users.username');
        }
    } else {
        $loginCountsQuery->groupBy(
            DB::raw('COALESCE(uu.Identifier, uc.Identifier)')
        );
    }

    $loginCounts = $loginCountsQuery->get();

    $totalLoginCount = $loginCounts->sum('login_count');
    $uniqueUserCount = $loginCounts->count();

        $transformedLoginCounts = [];
        if ($request->type === 'detailed') {
            $transformedLoginCounts = $loginCounts->groupBy('user_type')->mapWithKeys(function ($items, $userType) {
                return [$userType => $items->map(function ($item) {
                    return [
                        'id' => $item->id,
                        'name' => credential_decrypt($item->name),
                        'email' => credential_decrypt($item->email),
                        'username' => credential_decrypt($item->username),
                        'login_count' => $item->login_count,
                    ];
                })->toArray()];
            })->toArray();
        } else {
            $transformedLoginCounts = $loginCounts->mapWithKeys(function ($item) {
                return [$item->user_type => (string) $item->login_count];
            })->toArray();
        }

        if ($request->input('export', false)) {
            if ($request->type !== 'detailed') {
                return response()->json(['status' => 400, 'message' => 'Export is only available for detailed type.']);
            }

            $headings = ['ID', 'Name', 'Email', 'Username', 'Login Count'];
            $queryColumns = ['id', 'name', 'email', 'username', 'login_count'];

            $exportData = [];
            foreach ($loginCounts as $item) {
                $exportData[] = [
                    'id' => $item->id,
                    'name' => credential_decrypt($item->name),
                    'email' => credential_decrypt($item->email),
                    'username' => credential_decrypt($item->username),
                    'login_count' => $item->login_count,
                ];
            }

            if (empty($exportData) || !is_array($exportData[0])) {
                return response()->json(['status' => 400, 'message' => 'No data available for export.']);
            }

            $export = new LoginHistoryExport($request, $exportData, $headings, $queryColumns);
            $filePath = 'Data/Login_counts.xlsx';
            Excel::store($export, $filePath, 'public');

            $downloadLink = Storage::disk('public')->url($filePath);

            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }


    return response()->json([
        'total_login_count' => $totalLoginCount,
        'unique_login_count' => $uniqueUserCount,
        'login_counts' => $transformedLoginCounts,
    ]);
}


    public function expiredToken(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $user= Auth::user();
        $personal_access_tokens = DB::table('personal_access_tokens')->where('tokenable_id', $user->id)->get();
        $current_time=Carbon::now();
        if($personal_access_tokens->where('created_at', '<', $current_time)->count() < 0){
            return response()->json(['status' => 500, 'message' => 'Token Expired'], 500);
        }else{
            return response()->json(['status' => 200, 'message' => 'Token Valid'], 200);
        }
    }

    public function getUserTotalLoginCount($userId)
    {
        return PersonalAccessTokens::where('tokenable_id', $userId)
            ->count()+1;
    }
    public function deleteExitsToken($user)
    {
        if (config('concurrent_login') == "1") {
            $user->tokens()->delete();
        }
    }
    public function handleOtpToken($user,$request,$metadata)
    {
            if(($user->usertype_status) == 'N'){
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'User Type for this User is inactive',
                ], 500);
            }
            if ($user->status !== 'Y') {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'User is inactive',
                ], 500);
            }
            $this->deleteExitsToken($user);

            
            $rules = [
                'otp' => 'required',
            ];

            $validator = Validator::make($request->all(), $rules);
            if ($validator->fails()) {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'validations fails',
                        'errors' => $validator->errors()
                    ],
                    500
                );
            }else{
                $broker = Broker::first();
                $master_otp = $broker->master_otp;
                $this->deleteExitsToken($user);
                $token = generateTokenAll($user,$metadata);
                $cookie = cookie('token', $token, 60 * 24);

                if($master_otp == $request->otp){
                    $user->update([
                        'otp_sent_at' => now(),
                        'lockout_time' => null,
                        'failed_login_attempts' => 0,
                    ]);
                
                    SaveLoginHistory($user, $request);
                    return response()->json([
                        'status' => 200,
                        'access_token' => $token,
                        'token_type' => 'Bearer',
                        'return_data' => [],
                        'message' => config('Login.Error.Message') ?? 'OTP is Verified',
                    ], 200)->withCookie($cookie);
                }else{
                    if ($request->platform == 'customer') {
                        $user = Customer::where('email', credential_encrypt($request->user_name))->orwhere('mobile',credential_encrypt($request->user_name))->first();
                    } else { 
                         $user = User::where('email', credential_encrypt($request->user_name))->orwhere('mobile',credential_encrypt($request->user_name))->first(); 
                    } 
                    if ($user) {
                        if ($user->otp == $request->otp && now()> $user->lockout_time) {
                        $user->update([
                            'otp_sent_at' => now(),
                            'lockout_time' => null,
                            'failed_login_attempts' => 0,
                        ]);
                        SaveLoginHistory($user, $request);
                            return response()->json([
                                'status' => 200,
                                'access_token' => $token,
                                'token_type' => 'Bearer',
                                'return_data' => [],
                                'message' => config('Login.Error.Message') ?? 'OTP is Verified',
                            ], 200)->withCookie($cookie);

                    } else {
                        return $this->failedLoginAttempts($user,"Invalid OTP ");
                    }
                }else{
                    return response()->json([
                        'status' => 404,
                        'message' => config('Login.Error.Message') ?? 'Invalid OTP.',
                    ], 404);

                }
            }
        
        }
    }
    public function handleOtpSending($user)
    {
        if (!$user) {
            return Response::json([
                'status' => 500,
                'return_data' => [],
                'message' => config('Login.Error.Message') ?? 'User Does Not Exist',
            ], 500);
        }

        if ($user->usertype_status === 'N') {
            return Response::json([
                'status' => 500,
                'return_data' => [],
                'message' => config('Login.Error.Message') ?? 'User Type for this User is inactive',
            ], 500);
        }

        if ($user->status !== 'Y') {
            return Response::json([
                'status' => 500,
                'return_data' => [],
                'message' => config('Login.Error.Message') ?? 'User is inactive',
            ], 500);
        }

        $adharPanLinkStatus = $user->usertype == 2 && $user->pan_link_status != 1;

        if ($user->otp_sent_at && $user->otp_sent_at > now()->subSeconds(120)) {
            return Response::json([
                'status' => 429,
                'message' => config('Login.Error.Message') ?? 'Please wait 120 seconds before requesting a new OTP.',
            ], 429);
        }

        $otpMaster = OtpMaster::first();
        $resendOtpTime = $otpMaster->resend_otp_time ?? '';

        $broker = Broker::first();

        if($user->corporate_id){
            $otp = $user->otp;
        }else{
            $otp = mt_rand(100000, 999999);
        }
        $expiry = now()->addMinutes(10);
        Session::put('otp', $otp);

        if ($broker->is_email === 'Y') {
            $templates = TemplateModel::where('event', 'Send OTP')->get();
            if ($templates->isEmpty()) {
                $templates = TemplateModel::where('event', 'add_email_template')->get();
            }

            // foreach ($templates as $template) {
                $title = 'OTP Verification Mail'; //$template->title ?? 'OTP Verification Mail';
                $content = 'Use this OTP'; //$template->content ?? 'Please Add Template Content From Template';
                $body = 'Verify OTP'; //strip_tags(html_entity_decode($content)) ?: 'Default Body';

                $to_email = credential_decrypt($user->email);
                event(new EmailEvent($to_email, $otp, $expiry, $body, $title));
                EmailActivityLog($user, $otp, $expiry);

                $user->update(['otp' => $otp, 'otp_expiry' => $expiry]);

                return Response::json([
                    'status' => 200,
                    'return_data' => [],
                    'message' => config('Login.Error.Message') ?? 'OTP Sent to Your Email',
                ], 200);
            // }
        }

        if ($broker->is_sms === 'Y') {
            $user->update([
                'otp' => $otp,
                'otp_expiry' => $expiry,
                'otp_sent_at' => now(),
            ]);

            $template = SmsTemplate::where('title', 'Send OTP')->first();
            event(new SendOtpEvent($user, $otp, $template));

            return Response::json([
                'status' => 200,
                'return_data' => ['resendOtpTime' => $resendOtpTime],
                'message' => config('Login.Error.Message') ?? 'OTP sent successfully',
            ], 200);
        }

        return Response::json([
            'status' => 200,
            'return_data' => ['resendOtpTime' => $resendOtpTime],
            'message' => config('Login.Error.Message') ?? 'OTP Sent Successfully',
            'adharPanLinkStatus' => $adharPanLinkStatus,
        ], 200);
    }

    public function logoutAll(Request $request)
    {
        $request->validate([
            'token' => 'required|string',
        ]);
        $tokenParts = explode('|', $request->token);
        if (count($tokenParts) !== 2) {
            return response()->json([
                'status' => 400,
                'message' => config('Login.Error.Message') ?? 'Invalid token format',
            ], 400);
        }
        $tokenId = $tokenParts[0];

        $personalAccessToken = PersonalAccessToken::find($tokenId);

        if (!$personalAccessToken) {
            return response()->json([
                'status' => 404,
                'message' => config('Login.Error.Message') ?? 'Token not found',
            ], 404);
        }

        $user = $personalAccessToken->tokenable;

        if ($user) {
            $this->deleteExitsToken($user);

            return response()->json([
                'status' => 200,
                'message' => 'Logged out from all devices successfully',
            ], 200);
        } else {
            return response()->json([
                'status' => 401,
                'message' => config('Login.Error.Message') ?? 'Unauthorized or invalid token',
            ], 401);
        }
    }

    public static function ListallUserDetails(Request $request)
    {
        $usertype_id = $request->usertype;
        $user_id = $request->user_id;
        if (empty($usertype_id)) {

            return response()->json([
                'status' => 'error',
                'message' => 'Missing or empty id field',
            ], 500);
        }
        $users = User::select('users.id', 'users.username', 'users.mobile', 'users.email', 'usertypes.Identifier as usertype')
                ->join('usertypes', 'usertypes.id', '=', 'users.usertype')
                ->when($user_id, function ($query, $userId) {
                    return $query->where('users.id', $userId);
                })
                ->when($usertype_id, function ($query, $userTypeId) {
                    return $query->where('usertypes.id', $userTypeId);
                })
                ->get();

        if ($users->isEmpty()) {
            return response()->json([
                'status' => 'error',
                'message' => 'No matching id found in user_type table',
            ], 404);
        }

        $decryptedUsers = [];

        foreach ($users as $user) {
            $decryptedUser = [
                'user_id' => $user->id,
                'name' => credential_decrypt($user->name),
                'username' => credential_decrypt($user->username),
                'mobile_number' => credential_decrypt($user->mobile),
                'email_id' => credential_decrypt($user->email),
                'usertype' => $user->usertype,
                'unique_key' => credential_decrypt($user->mobile),
            ];

            $decryptedUsers[] = $decryptedUser;
        }

        if ($decryptedUsers) {
            return response()->json([
                'status' => 'success',
                'data' => $decryptedUsers,
            ], 200);
        } else {
            return response()->json([
                'status' => 'error',
                'message' => config('Login.Error.Message') ?? 'No data found'
            ], 500);
        }
    }

    public function getLoginCountForMappedUsers(Request $request)
    {
        $auth = Auth::user();
        $allMappedUsers = getUserLowerHierarchyWithMapping($auth->id, $auth->usertype);

        $output = [];
        $users = User::select('id', 'name')->whereIn('id', $allMappedUsers)->get();

        $startDate = request()->start_date ?? Carbon::today()->toDateString();
        $endDate = request()->end_date ?? Carbon::today()->toDateString();

        $startDateTime = Carbon::parse($startDate)->startOfDay();
        $endDateTime = Carbon::parse($endDate)->endOfDay();

        // Fetch login counts for all users in one query
        $loginCounts = LoginHistory::select('user_id', DB::raw('count(*) as total'))
            ->whereIn('user_id', $allMappedUsers)
            ->whereBetween('created_at', [$startDateTime, $endDateTime])
            ->groupBy('user_id')
            ->pluck('total', 'user_id'); // This will give [user_id => total_logins]

        foreach ($users as $u) {
            $output[] = [
                'id' => $u->id,
                'name' => credential_decrypt($u->name),
                'login_count' => $loginCounts[$u->id] ?? 0
            ];
        }

        if (!empty($output)) {
            return response()->json([
                'status' => 'success',
                'message' => 'Data Found',
                'data' => $output,
                'data_count' => count($output)
            ], 200);
        } else {
            return response()->json([
                'status' => 'failed',
                'message' => 'Data Not Found',
                'data' => $output ?? []
            ], 500);
        }
    }

    public function fetchMappedUserDetails(Request $request)
    {
        $auth = Auth::user();
        $perPage = $request->perPage ?? 10;
        $allMappedUsers = getUserLowerHierarchyWithMapping($auth->id, $auth->usertype);

        $output = [];

        $startDate = request()->start_date ?? Carbon::today()->toDateString();
        $endDate = request()->end_date ?? Carbon::today()->toDateString();

        $startDateTime = Carbon::parse($startDate)->startOfDay();
        $endDateTime = Carbon::parse($endDate)->endOfDay();

        $users = User::select(
            'users.id',
            'users.name',
        )
            ->leftJoin('login_history', 'users.id', '=', 'login_history.user_id')
            ->with(['roles:id,name,user_type', 'lobs:id,lob_name,lob'])
            ->whereBetween('login_history.created_at', [$startDateTime, $endDateTime])
            ->selectRaw('COUNT(login_history.user_id) as login_count')  // Get login count
            ->selectRaw('MAX(login_history.created_at) as latest_login')  // Get latest login created_at
            ->groupBy('users.id', 'users.name')  // Group by all selected fields
            ->whereIn('users.id', $allMappedUsers)
            ->orderBy('latest_login', 'desc')  // Order by the latest login
            ->paginate(10);

        $output = [];

        $startDate = request()->start_date ?? Carbon::today()->toDateString();
        $endDate = request()->end_date ?? Carbon::today()->toDateString();

        $startDateTime = Carbon::parse($startDate)->startOfDay();
        $endDateTime = Carbon::parse($endDate)->endOfDay();

        foreach ($users as $key => $user) {

            $lobNamesArray = $user->lobs->pluck('lob')->toArray();
            $lobNames = implode(",", $lobNamesArray);

            $output[] = [
                'Sr No' => ++$key,
                'id' => $user->id ?? null,
                'name' => credential_decrypt($user->name) ?? null,
                'Role' => $user->roles[0]->name ?? null,
                'Lob' => $lobNames ?? "",
                'Last Login Date' => $user->latest_login ?? null,
                'Login Count' => $user->login_count ?? 0
            ];
        }

        if ($request->has('export') && $request->export == true) {
            $fileName = 'user_login_report.xlsx';
            Excel::store(new UserLoginReportExport($output), $fileName, 'public');
            $downloadUrl = Storage::disk('public')->url($fileName);
        }

        if (!empty($output)) {
            return response()->json([
                'status' => 'success',
                'message' => 'Data Found',
                'data' => $output,
                'excel_download_link' => $downloadUrl ?? null,
                'pagination' => [
                    'total_records' => $users->total(),
                    'total_pages' => $users->lastPage(),
                    'current_page' => $users->currentPage(),
                    'per_page' => $perPage,
                ],
            ], 200);
        } else {
            return response()->json([
                'status' => 'failed',
                'message' => config('Login.Error.Message') ?? 'Data Not Found',
                'data' => $output ?? []
            ], 500);
        }
    }

    public function loginTimeLogs(Request $request)
    {
        $validator = Validator::make($request->all(), [
            "user_id" => "required"
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }

        $startDate = $request->start_date ?? Carbon::today()->toDateString();
        $endDate = $request->end_date ?? Carbon::today()->toDateString();

        $startDateTime = Carbon::parse($startDate)->startOfDay();
        $endDateTime = Carbon::parse($endDate)->endOfDay();

        $login_data = LoginHistory::select('created_at')->where('user_id', $request->user_id)
            ->whereBetween('created_at', [$startDateTime, $endDateTime])
            ->get();

        if (!empty($login_data)) {
            return response()->json([
                'status' => 'success',
                'message' => 'Data Found',
                'data' => $login_data,
                'data_count' => count($login_data)
            ], 200);
        } else {
            return response()->json([
                'status' => 'failed',
                'message' => config('Login.Error.Message') ?? 'Data Not Found',
                'data' => $login_data ?? []
            ], 500);
        }
    }

    public function failedLoginAttempts($user, $message)
    {
        if ($user->failed_login_attempts > 2) {
            $user->update([
                'lockout_time' => now()->addMinutes(10),
            ]);
        }

        if ($user->lockout_time && $user->lockout_time > now()) {
            return response()->json([
                'status' => 429,
                'return_data' => [],
                'message' => config('Login.Error.Message') ?? 'Your Account has been locked,try again after.' . $user->lockout_time,
            ], 429);
        }

        $user->failed_login_attempts += 1;
        $user->save();

        return response()->json([
            'status' => 500,
            'return_data' => [],
            'message' =>  config('Login.Error.Message') ?? $message . 'Attempts left: ' . (3 - $user->failed_login_attempts),
        ], 500);
    }

    private function makeFileUrl(?string $path)
    {
        if (!$path) {
            return null;
        }
    
        if (filter_var($path, FILTER_VALIDATE_URL)) {
            return $path;
        }
    
        $isS3 = config('dashboard_storage_disk') === 's3';
    
        if ($isS3) {
            $s3Root = trim(env('AWS_ROOT'), '/') . '/dashboard/storage/';
            return Storage::disk('s3')->temporaryUrl(
                $s3Root . $path,
                now()->addMinutes(15)
            );
        }
    
        return Storage::disk('public')->url($path);
    }

    public function customerPolicyExpireData(Request $request)
    {
        $customers = Customer::join('customer_policy_expire', 'customer_policy_expire.customer_id', '=', 'customer.id')
            ->join('lob_master', 'lob_master.id', '=', 'customer.lob_id')
            ->select('first_name as email_id','email as act_email_id','mobile','NAME as name','policy_no','policy_end_date','l.lob')
            ->get();

        if ($customers) {
            foreach ($customers as $key => $customer) {
    
                $output[] = [
                    'Sr No' => ++$key,
                    'email_id' => $customer->email_id ?? null,
                    'name' => credential_decrypt($customer->name) ?? null,
                    'act_email_id' => credential_decrypt($customer->act_email_id) ?? null,
                    'mobile' => credential_decrypt($customer->mobile) ?? null,
                    'policy_no' => $customer->policy_no ?? null,
                    'policy_end_date' => $customer->policy_end_date ?? null,
                    'lob' => $customer->lob ?? null
                ];
            }

            return response()->json([
                'status' => 200,
                'data' => $output,
            ], 200);
        }
    }


}


