<?php

use App\Http\Controllers\Plugins\PHPGangsta_GoogleAuthenticator;
use App\Models\DataExportLog;
use App\Models\LoginHistory;
use App\Models\RoleCodeMapping;
use App\Models\StagemasterModel;
use App\Models\substagemaster;
use App\Models\User;
use App\Models\Role;
use App\Models\userTypes;
use SimpleSoftwareIO\QrCode\Facades\QrCode;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use App\Models\EmailActivityLog;
use App\Models\SmsActivityLog;
use Illuminate\Support\Facades\Log;
use Illuminate\Http\JsonResponse;
use App\Models\SSO;
use App\Models\lobMaster;
use App\Models\ThirdPartyLogs;
use App\Models\UserMapping;
use App\Models\Customer;
use App\Models\MisColumnView;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Str;

define('CIPHER_ALGO', 'aes-256-gcm');
define('IV_LENGTH', 12);     
define('TAG_LENGTH', 16);    
function validateToken($token): bool
{
    if (!$token) {
        return false;
    }
    $ssoRecord = SSO::where('sso_api_token', $token)->first();
    if (!$ssoRecord) {
        return false;
    }

    $expiryMinutes = (int) config('auth.token_expiry', 30);
    $expiresAt = $ssoRecord->expires_at ?? $ssoRecord->created_at->addMinutes($expiryMinutes);

    if (now()->greaterThan($expiresAt)) {
        $ssoRecord->update(['status' => 'N']);
        return false;
    }

    return true;
}
if (!function_exists('getAbilityValue')) {
    function getAbilityValue($token, string $prefix): ?string
    {
        return collect($token->abilities)
            ->first(fn($ability) => str_starts_with($ability, $prefix));
    }
}
if (!function_exists('getParsedAbilityValue')) {
    function getParsedAbilityValue($token, string $prefix): ?string
    
    {
        $ability = getAbilityValue($token, $prefix);
        return $ability ? explode(':', $ability)[1] ?? null : null;
    }
}
if (!function_exists('getUserTypeFromToken')) {
    function getUserTypeFromToken()
    {
        $token = Auth::user()->currentAccessToken();
        if (!$token) {
            return null;
        }
        $prefix = 'usertypeIdentifier:';
        $ability = getAbilityValue($token, $prefix);
        return $ability ? explode(':', $ability)[1] ?? null : null;
    }
}
function getUserTypeIdByIdentifier($identifier){
    return DB::table('usertypes')
    ->where('Identifier',$identifier)
    ->where('is_active', 'Y')
    ->value('id');
}

function makeFileUrl(?string $path)
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

if (! function_exists('generateTokenAll')) {
    function generateTokenAll($user, array $metadata = [])
    {
        $identifier =getUserTypeIdentifier($user->usertype);
        $metadatanew=array_merge($metadata,["usertypeIdentifier:$identifier"]);
        $token = $user->createToken('token',$metadatanew)->plainTextToken;
        return $token;
    }
}
function getRoleIdByName($roleName)
{
    return DB::table('roles')
        ->where('name', $roleName)
        ->value('id');
}

function getRoleLowerHierarchy($roleId,$userType)
{
    $role = Role::select('id','name','user_type','reporting_role')->find($roleId);
    $roles = [];

    if ($role) {
        $roles = getRoleChildren($role,$userType);
    }

    return $roles;
}

function getRoleChildren($role,$userType)
{
    $children = $role->children($userType)->select('id', 'name', 'user_type', 'reporting_role')->get();


    $roles = [];

    foreach ($children as $child) {
        if ($role->id != $child->id) {
        $roles[] = $child;
        $roles = array_merge($roles, getRoleChildren($child,$userType));
        }
    }

    return $roles;
}

function getRoleUpperHierarchy($roleId)
{
    $role = Role::select('id', 'name', 'user_type', 'reporting_role')->find($roleId);
    $roles = [];

    while ($role && $role->parent) {
        $parent = Role::select('id', 'name', 'user_type', 'reporting_role')->find($role->reporting_role);
        if ($parent) {
            $roles[] = $parent->toArray();
        }
        $role = $parent;
    }

    return $roles;
}

function getRoleUpperHierarchyTillLoggedInUserForReportingUser($roleId, $roleIdOfLoggedInUser)
{

    $role = Role::select('id', 'name', 'user_type', 'reporting_role')->find($roleId);
    $roles = [];
    if ($role) {
        $roles[] = $role->toArray(); // Add the current role first
    }
    
    do {
        if ($role && $role->parent) {
            $parent = Role::select('id', 'name', 'user_type', 'reporting_role')->find($role->reporting_role);
            if ($parent) {
                $roles[] = $parent->toArray();
            }
            $role = $parent;
        } else {
            break;
        }
    } while ($role && $role->id != $roleIdOfLoggedInUser);

    return $roles;
}

function getRoleUpperHierarchyTillLoggedInUser($roleId,$roleIdOfLoggedInUser){

    $role = Role::select('id', 'name', 'user_type', 'reporting_role')->find($roleId);
    $roles = [];

    do {
        if ($role && $role->parent) {
            $parent = Role::select('id', 'name', 'user_type', 'reporting_role')->find($role->reporting_role);
            if ($parent) {
                $roles[] = $parent->toArray();
            }
            $role = $parent; 
        } else {
            break; 
        }
    } while ( $role && $role->id != $roleIdOfLoggedInUser  );

    return $roles;
}

function getUserUpperHierarchy($userId)
{
    $user = User::select('id','reportingto')->find($userId);


    $users = [];

    while ($user && $user->parent) {
        $parent = user::select('id','reportingto')->find($user->reportingto);

        if ($parent) {
            $users[] = $parent->toArray();
        }
        $user = $parent;
    }

    return $users;
}

function getUserLowerHierarchyForLoginCount($userId,$userType=1)
{

    $newHierarchyLogic = config('app.new_hierarchy_logic', false);

    if ($newHierarchyLogic) {
        if ($userType == '3') {
            return [];
        }
        $user = User::select('id', 'path', 'employee_code')
            ->find($userId);

        if (! $user || empty($user->path)) {
            return [];
        }
        $result = [$user->toArray()];

        if ($userType == '2') {
            $children = User::select('id', 'employee_code')
                ->childrenOf($user)
                ->get()
                ->toArray();
        } else {
            $children = User::select('id', 'employee_code')
                ->descendantsOf($user)
                ->orderBy('path')
                ->get()
                ->toArray();
        }
        return array_merge($result, $children);
    }else {
        
    $user = User::select('id','reportingto','employee_code')->find($userId);
    $users = [];

    if ($user) {
        $users[] = $user;

        $users = array_merge($users, getUserChildren($user, $userType));  // Adding current user also in this function
    }

    return $users;
    }
}
function getUserLowerHierarchyOld($userId, $userType = 1)
{    
    $users = [];
    switch ($userType) {
        case '3':
            $users = [];
            break;
        case '2':
            $users = User::select('id', 'reportingto', 'employee_code', 'old_user_id')->where('reportingto', $userId)->get()->toArray();
            break;
        default:
            $user = User::select('id', 'reportingto', 'employee_code', 'old_user_id')->find($userId);
            if ($user) {
                $users = getUserChildren($user, $userType);
            }
            break;
    }

    return $users;
}

function getUserLowerHierarchy($userId, $userType = 1, $userStatus = 'All')
{
    // if ($userType == 3) {
    //     return [];
    // }

    $cacheKey = 'user_hierarchy_map_' . $userStatus;

    $allUsers = Cache::remember($cacheKey, 3600, function () use ($userStatus) {

        $query = DB::table('users')
            ->select('id', 'reportingto', 'employee_code', 'old_user_id');

        if ($userStatus != 'All') {
            $query->where('status', $userStatus);
        }

        $users = $query->get();

        $map = [];

        foreach ($users as $user) {
            $map[$user->reportingto][] = (array) $user;
        }

        return $map;
    });
    
    if ($userType == 2) {
        return $allUsers[$userId] ?? [];
    }

    return getUserChildrenIterative($userId, $allUsers);
}




function getUserChildrenIterative($userId, $allUsers)
{
    $result = [];
    $stack = [$userId];

    while (!empty($stack)) {
        $current = array_pop($stack);

        if (!isset($allUsers[$current])) {
            continue;
        }

        foreach ($allUsers[$current] as $child) {
            $result[] = $child;
            $stack[] = $child['id'];
        }
    }

    return $result;
}



function getUserLowerHierarchyWithMapping($userId, $userType = 1)
{
    $newHierarchyLogic = config('app.new_hierarchy_logic', false);

    if ($newHierarchyLogic) {

        if ($userType == '3') {
            return [];
        }
        $user = User::select('id', 'path', 'employee_code')
            ->find($userId);

        if (! $user || empty($user->path)) {
            return [];
        }

        if ($userType == '2') {
            $users = User::select('id', 'employee_code')
                ->childrenOf($user)
                ->get()
                ->toArray();
        } else {
            $users = User::select('id', 'employee_code')
                ->descendantsOf($user)
                ->orderBy('path')
                ->get()
                ->toArray();
        }

        $employeeIds = array_column($users, 'id');

        if ($userType != 1) {
            return $employeeIds;
        }

        $employeeIds[] = $userId;

        $employeeCodes = array_column($users, 'employee_code');
        $employeeCodes[] = $user->employee_code;

        $finalMappingData = getMapPosPartner($employeeCodes);

        $mappingIds = array_column($finalMappingData, 'id');

        return array_values(array_unique(
            array_merge($employeeIds, $mappingIds)
        ));
    }else {
        $user = User::select('id','reportingto','employee_code')->find($userId);
        $users = [];

        if ($user) {
            $users = getUserChildren($user,$userType);
        }

        
        $employeeIds = array_map(function ($user) {
            return $user['id'];
        }, $users);

        if ($userType !=1) {
             return $employeeIds;
        } else {
        $employeeIds=array_merge($employeeIds,[$userId]);
    
             $modelIdUsersEmployeeCode = User::whereIn('id', $employeeIds)->select('id', 'name', 'reportingto','employee_code')->get()->toArray();
             if($modelIdUsersEmployeeCode){
                foreach($modelIdUsersEmployeeCode as $key=>$value){
                    $UserHierarchyEmpCode[]=$value['employee_code'];
                }
            }
            $finalMappingData = getMapPosPartner($UserHierarchyEmpCode);
            $firstArrayIds = array_column($finalMappingData, 'id');
            $mappingIds = array_unique(array_merge($firstArrayIds, $employeeIds));
           
            
            return $mappingIds;
        }
    
    }
}

function activeRoleCodeMappingUser(){
    $auth = Auth::user();
    $roleId = $auth->roles()->pluck('id')->first();

    $rows = RoleCodeMapping::where('role_id',$roleId)
        ->where('status',1)
        ->get(['parameter_name','parameter_value']);

    $output = [];

    foreach($rows as $row){
        $names = explode(',', $row->parameter_value); // split by comma
        foreach($names as $name){
            if(array_key_exists($row->parameter_name,$output)){
                $output[$row->parameter_name] .= ',' . trim($name);
            }else{
                $output[$row->parameter_name] = trim($name);
            }
        }
    }
    return $output;
}


function getUserChildren($user,$userType)
{

    $children = $user->children($userType)->select('id', 'reportingto','employee_code','old_user_id')->get();

    $users = [];

    foreach ($children as $child) {
        if ($user->id != $child->id) {
            $users[] = $child;
            $users = array_merge($users, getuserChildren($child, $userType));

        }
    }

    return $users;
}
function credential_encrypt($data)
{
    if (!empty($data)) {
        $data = is_array($data) ? json_encode($data) : $data;
        list($key, $iv) = array_values(getKeys());
        $tag = null;
        $cipherText = openssl_encrypt(
            $data,
            'aes-256-gcm',
            $key,
            OPENSSL_RAW_DATA,
            $iv,
            $tag
        );
        return base64_encode($iv . $tag . $cipherText);
    }
    return $data;
}

if (!function_exists('encrypt_decrypt_password_remote')) {
    function encrypt_decrypt_password_remote($string, $type = 'E')
    {
        $encrypt_method = "AES-256-CBC";

        $secret_key = config('pos_onboarding_encryption_key');
         
        $secret_iv  = md5(md5($secret_key));

        $key = hash('sha256', $secret_key);
        $iv  = substr(hash('sha256', $secret_iv), 0, 16);

        if ($type === 'E') {
            $encrypted = openssl_encrypt($string, $encrypt_method, $key, 0, $iv);
            return base64_encode($encrypted);
        } elseif ($type === 'D') {
            return openssl_decrypt(base64_decode($string), $encrypt_method, $key, 0, $iv);
        }

        return false;
    }
}

function credential_decrypt($encryptedData)
{
    if (!empty($encryptedData)) {
        try {
            $data = base64_decode($encryptedData);
            list($key, $iv) = array_values(getKeys());
            $tag = substr($data, 12, 16);
            $cipherText = substr($data, 28);

            $decryptedData = openssl_decrypt(
                $cipherText,
                'aes-256-gcm',
                $key,
                OPENSSL_RAW_DATA,
                $iv,
                $tag
            );

            if ($decryptedData === false) {
                return $encryptedData;
            }
            return $decryptedData;
        } catch (Exception $e) {
            return $encryptedData;
        }
    }
    return $encryptedData;
}
function getKeys()
{
    return [
        'key' => base64_decode(env('APP_KEY')),
        'iv' => base64_decode('RBr5xS8U4WSNhE+b'),
    ];
}
function generateRandomPassword($length = 8)
{
    $lowercase = 'abcdefghijklmnopqrstuvwxyz';
    $uppercase = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
    $numbers = '0123456789';
    $special = '@#';

    $randomPassword = '';
    $randomPassword .= $lowercase[rand(0, strlen($lowercase) - 1)];
    $randomPassword .= $uppercase[rand(0, strlen($uppercase) - 1)];
    $randomPassword .= $numbers[rand(0, strlen($numbers) - 1)];
    $randomPassword .= $special[rand(0, strlen($special) - 1)];

    $allCharacters = $lowercase . $uppercase . $numbers . $special;
    $remainingLength = $length - 4;
    for ($i = 0; $i < $remainingLength; $i++) {
        $randomPassword .= $allCharacters[rand(0, strlen($allCharacters) - 1)];
    }
    $randomPassword = str_shuffle($randomPassword);

    return $randomPassword;
}
function SaveLoginHistory($user, $request)
{
    $login = new LoginHistory();
    $login->user_id = $user->id;
    $login->ip = $request->ip() ?? $request->ip;
    $login->browser = $request->header('User-Agent') ?? $request->browser;
    $login->logged_in_by = $request->type ?? '0';
    $login->usertype = $user->usertype ?? null;
    $login->save();
}

if (!function_exists('getUUID')) {
    function getUUID($trace_id = null)
    {
        try {
            $data = random_bytes(16);
        } catch (\Exception $e) {
            $data = openssl_random_pseudo_bytes(16);
        }

        $data[6] = chr(ord($data[6]) & 0x0f | 0x40);
        $data[8] = chr(ord($data[8]) & 0x3f | 0x80);
        $generated_UUID = vsprintf('%s%s-%s-%s-%s-%s%s%s', str_split(bin2hex($data), 4));

        return $generated_UUID;
    }
}

if (!function_exists('getDecryptedPayload')) {
    function getDecryptedPayload($encrypted)
    {
        $key = config('Payload.Secret.Key'); // same 32-char key
        $iv = config('Payload.Secret.IV'); // same 16-char IV
        $decrypted = openssl_decrypt(
            base64_decode($encrypted),
            'AES-256-CBC',
            $key,
            OPENSSL_RAW_DATA,
            $iv
        );

        // $data = json_decode($decrypted, true);
        return $decrypted;
    }
}

if (!function_exists('getEncryptedPayload')) {
    function getEncryptedPayload($data)
    {
        $key = config('Payload.Secret.Key'); // same 32-char key
        $iv = config('Payload.Secret.IV');   // same 16-char IV

        // Agar data array ya object hai to usse JSON mein convert karo
        if (is_array($data) || is_object($data)) {
            $data = json_encode($data);
        }

        $encrypted = openssl_encrypt(
            $data,
            'AES-256-CBC',
            $key,
            OPENSSL_RAW_DATA,
            $iv
        );

        return base64_encode($encrypted);
    }
}



if (!function_exists('addTokenToHeader')) {
    function addTokenToHeader($headers, $apiUrl)
    {
        $tokenService = app(\App\Services\ThirdPartyTokenService::class);
        $token = $tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;
        return $headers; 
    }
}
// Helper function to convert date to 'dd/mm/yyyy' format
function formatDateForDisplay($date)
{
    return \Carbon\Carbon::createFromFormat('Y-m-d', $date)->format('d/m/Y');
}


/**
 * all key value should be wrappeed in data variable
 * status code madatory
 * message madotory
 * data optional in failed cases
 */

if (!function_exists('requestResponseMessage')) {
    function requestResponseMessage($data)
    {
        if (!empty($data['data'])) {
            if ($data['status'] == 200) {
                return response()->json([
                    'status'  => $data['status'],
                    'message' => $data['message'] ?? '',
                    'data'    => $data['data'] ?? ''
                ], $data['status']);
            } else {
                return response()->json([
                    'status'  => $data['status'] ?? '',
                    'message' => $data['message'] ?? 'API error',
                    'error'   => $data['error'] ?? ''
                ], $data['status']);
            }
        }
        
        return response()->json([
            'status'  => $data['status'] ?? '',
            'message' => $data['message'] ?? 'API error',
            'error'   => $data['error'] ?? ''
        ], $data['status'] ?? 500);
    }
}

if (!function_exists("getReportingUsers")) {
    function getReportingUsers($user_id)
    {
        $user = User::find($user_id);
        $users = $user->getReportingUsers();
        dd($users);
        return $users;
    }
}
function generateQrcode($secret = null)
{
    $ga = new PHPGangsta_GoogleAuthenticator();
    if ($secret == null) {
        $secret = $ga->createSecret();
    }
    $qrCodeUrl = $ga->getQRCodeGoogleUrl('Dashboard 2.0', $secret);

    $qrCodeSvg = QrCode::format('svg')->size(200)->errorCorrection('H')->generate("otpauth://totp/Dashboard 2.0?secret=" . $secret);
    $qrCodeBase64 = base64_encode($qrCodeSvg);
    $qrcode = 'data:image/svg+xml;base64,' . $qrCodeBase64;

    return ['QrCode' => $qrCodeUrl, 'secret' => $secret];
}
/**
 * Get an array of user id's mapped to a given array of employee codes,
 * filtered by usertype of 'P' or 'Partner'.
 *
 * @param array $data an array of employee codes
 * @return array an array of user id's
 */
if(!function_exists('getMapPosPartner')) {
    function getMapPosPartner($data = [])
    {
        $posParenterId = userTypes::select('id')->whereIn('Identifier', ['P', 'Partner'])->get()->toArray();
        $result = User::select('id','usertype','old_user_id')->whereIn('employee_code', $data)->whereIn('usertype', $posParenterId)->get()->toArray();
        // $userQuery = User::select('id')
        //     ->whereIn('employee_code', $data)
        //     ->whereIn('usertype', [2, 3]);

        // $mappingQuery = UserMapping::select('user_id as id')
        //     ->whereIn('employee_code', $data)
        //     ->whereIn('user_type', [2, 3]);

        // $result = $userQuery->union($mappingQuery)->get()->pluck('id')->unique()->values();

        return $result;
    }
}
function checkUserActivity(Request $request)
{
    $user = auth()->user();
    if ($user->usertype !="5") {
        $user = $user->LeftJoin('usertypes', 'usertypes.id', '=', 'users.usertype')
            ->where('users.usertype', $user->usertype)
            ->first();

    }
    if ($user->is_active == 'N') {
        $request->user()->currentAccessToken()->delete();
        return response()->json(
            [
                'status' => 500,
                'return_data' => [],
                'message' => 'User logged out and token invalidated due to inactive usertype'
            ],
            500
        );
    }

    return null;
}

if(!function_exists('getUserTypeIdentifier')){
    function getUserTypeIdentifier($userTypeId)
    {
        return  userTypes::where('id', $userTypeId)->pluck('Identifier')->first();;
    }
}

if (!function_exists('validateUserTypeForPlatform')) {
    function validateUserTypeForPlatform($user, $platform)
    {
        // $userTypeIdentifier = getUserTypeIdentifier($user->usertype);
        $userTypeIdentifier = $user->userType->Identifier;
        
        if ($userTypeIdentifier == 'U' && $platform != 'customer' && $user->userMappings->isNotEmpty()) {
            return null;
        }
        if ($userTypeIdentifier == 'U' && $platform != 'customer') {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Customer Usertype is not allowed',
            ], 500);
        }

        if ($userTypeIdentifier != 'U' && $platform == 'customer') {
            $customerMappingTabel = false;
            if ($user->userMappings->isNotEmpty()) {
                 foreach ($user->userMappings as $key => $value) {
                    if ($value->user_type == '5') {
                        $customerMappingTabel = true;
                    }
                }
            }
            if ($customerMappingTabel == false) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Only Customer usertype is allowed',
                ], 500);
            }
        }

        return null; // No validation error
    }
}

if (!function_exists('getWsData')) {
    function getWsData($Url = '', $Inputs = array(), $headers = array(), $additionalData = array())
    {
        $ch = curl_init($Url);
        // Set the cURL options
        curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
        curl_setopt($ch, CURLOPT_POST, true);
        curl_setopt($ch, CURLOPT_HTTPHEADER, $headers);
        curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query($Inputs));

        $response = curl_exec($ch);

        // Check for errors
        if (curl_errno($ch)) {
            $error = 'Error:' . curl_error($ch);
            curl_close($ch);
            return $error;
        } else {
            // Close cURL session
            curl_close($ch);
            // Return the response
            return $response;
        }
    }
}

if (!function_exists('decryptUserData')) {
    function decryptUserData($user, $fields)
    {
        foreach ($fields as $field) {
            if (!empty($user->$field)) {
                $user->$field = credential_decrypt($user->$field);
            }
        }
        return $user;
    }
}

if (!function_exists('logApiRequestResponse')) {
    function logApiRequestResponse($url, $method, $requestData, $responseData, $statusCode, $headers,$apiType=null)
    {
        if (config('store_logs_in_mysql') == true) {
            DB::table('logs_api_table')->insert([
                'url' => $url,
                'method' => $method,
                'headers' => json_encode($headers),
                'request' => json_encode($requestData),
                'response' => json_encode($responseData),
                'status_code' => $statusCode,
                'created_at' => now(),
                'updated_at' => now(),
                'api_type' => $apiType,
            ]);
        }

        if (config('store_logs_in_mongodb') == true) {

            DB::connection('mongodb')->table('third-party-logs')->insert([
                'url' => $url,
                'method' => $method,
                'headers' => json_encode($headers),
                'request' => json_encode($requestData),
                'response' => json_encode($responseData),
                'status_code' => $statusCode,
                'created_at' => now(),
                'updated_at' => now(),
                'api_type' => $apiType,
            ]);
        }
    }
}
if(!function_exists('MappedPosUsers'))
{
    function MappedPosUsers($UserId, $AllUsers,$posUsertypeId): array
    {
        $PosUsersArr = [];
        if(!empty($AllUsers))
        {

            $AllUsers_arr=$AllUsers->toArray();
            foreach($UserId as $user)
            {
                $index = array_search($user, array_column($AllUsers_arr, 'id'));
                $currentUserEmployeeCode[]=$AllUsers_arr[$index]->employee_code??'';
            }


            // foreach($AllUsers as $user)
            // {
            //     if(in_array($user->id,$UserId))
            //     {
            //         $currentUserEmployeeCode = empty($user->employee_code) ? null : $user->employee_code;
            //         break;
            //     }
            // }
            foreach ($AllUsers as $key => $value) {
                if(in_array($value->employee_code ,$currentUserEmployeeCode) && $value->usertype == $posUsertypeId && !empty($value->employee_code))
                {
                    $PosUsersArr[] = [
                        'id' => $value->id,
                        'usertype' => $value->usertype
                    ];
                }
            }
        }
        return $PosUsersArr;
    }
}

/*
 *  Function to check if user is admin or not if reportingto is 0 then user is admin or in users table is_admi ncolumn is used to determisn is users is admin
 *  @param $UserId
 *  @return bool
 */
if (!function_exists('UserIsAdmin')) {
    function UserIsAdmin(int $UserId)
    {
        $user = \App\Models\User::where('id',$UserId)->first();
        if(empty($user))
        {
            return false;
        }

        if($user)
        {
            if($user->reportingto == 0 || $user->is_admin == 'Y')
            {
                return true;
            }
            else
            {
                return false;
            }

        }
    }
}
if (!function_exists('RoleHierarchy')) {
    function RoleHierarchy($roleId, $userTypeId)
    {
        $roles = DB::table('roles')
            ->select('id', 'reporting_role', 'user_type')
            ->where('reporting_role', $roleId)
            ->where('user_type', $userTypeId)
            ->get();
        $roleIds = $roles->pluck('id')->toArray();
        foreach ($roles as $role) {
            $childRoleIds = RoleHierarchy($role->id, $role->user_type);
            $roleIds = array_merge($roleIds, $childRoleIds);
        }

        return $roleIds;
    }
}

/*
 * Function To Get All the Usertypes And Employee If Admin or Not
 * @param $UserID
 * @param $UserTypeId
 * @return array
 */
if (!function_exists('userHierarchy')) {
    function userHierarchy($roleId, $userTypeId): array
    {
            $allUsers = DB::table('users')
                ->select('id', 'reportingto', 'usertype','employee_code')
                ->get();
            $result = [];
            $posUsertypeId = null;
            $UsertypeId  = DB::select('select id,Identifier from usertypes');
            foreach($UsertypeId as $usertypeId)
            {
                if($usertypeId->Identifier == 'P')
                {
                    $posUsertypeId = $usertypeId->id;
                }
            }

            $userIsAdmin = UserIsAdmin($roleId);
            $posUsersArrForAdmin = [];
            if ($userIsAdmin) {
                foreach ($allUsers as $user) {
                    if ($user->usertype == $userTypeId) {
//                        todo:if employee admin then show all employee pos partner data
//                        todo:
                        $employeeMappedPosUsers = MappedPosUsers([$user->id], $allUsers,$posUsertypeId);
                        foreach ($employeeMappedPosUsers as $employeeMappedPosUser) {
                            $posUsersArrForAdmin[] = $employeeMappedPosUser['id'];
                        }
                    }
                }
                return $result[] = [
                    'isAdmin' => true,
                    'id' => $roleId,
                    'usertype' => $userTypeId,
                    'PosUsers' => $posUsersArrForAdmin
                ];
            }

            $result = buildHierarchy($allUsers, $roleId, $userTypeId);
            $result[] = [
                'id' => $roleId,
                'usertype' => $userTypeId
            ];
            $ids = array_column($result, 'id');
            $PosUsersArr = [];
            $MappedPosUsers = MappedPosUsers($ids, $allUsers,$posUsertypeId);
            if(!empty($MappedPosUsers))
            {
                $PosUsersArr = $MappedPosUsers;
            }
            $result = array_merge($result, $PosUsersArr);
            return $result;
    }

}
function buildHierarchy($users, $roleId, $userTypeId)
{
    $userData = [];

    // foreach ($users as $user) {
    //     if ($user->reportingto == $roleId && $user->usertype == $userTypeId) {
    //         $userData[] = ['id' => $user->id, 'usertype' => $user->usertype];

    //         $childRoleData = buildHierarchy($users, $user->id, $user->usertype);

    //         if (!empty($childRoleData)) {
    //             $userData = array_merge($userData, $childRoleData);
    //         }
    //     }
    // }
    return $userData;
}
/**
 * XML2Array: A class to convert XML to array in PHP
 * It returns the array which can be converted back to XML using the Array2XML script
 * It takes an XML string or a DOMDocument object as an input.
 *
 * Usage:
 *       $array = XML2Array::createArray($xml);
 */
class XML2Array
{
    private static $xml = null;
    private static $encoding = "UTF-8";

    /**
     * Convert an XML to Array
     *
     * @param string $node_name - name of the root node to be converted
     * @param array $arr - aray to be converterd
     *
     * @return DOMDocument
     */
    public static function &createArray($input_xml)
    {
        $xml = self::getXMLRoot();
        libxml_use_internal_errors(true);
        if (is_string($input_xml)) {
            $parsed = $xml->loadXML($input_xml);
            if (!$parsed) {
                throw new Exception(
                    "[XML2Array] Error parsing the XML string."
                );
            }
        } else {
            if (get_class($input_xml) != "DOMDocument") {
                throw new Exception(
                    "[XML2Array] The input XML object should be of type: DOMDocument."
                );
            }
            $xml = self::$xml = $input_xml;
        }
        $array[$xml->documentElement->tagName] = self::convert(
            $xml->documentElement
        );
        self::$xml = null; // clear the xml node in the class for 2nd time use.
        return $array;
    }

    private static function getXMLRoot()
    {
        if (empty(self::$xml)) {
            self::init();
        }

        return self::$xml;
    }

    /**
     * Initialize the root XML node [optional]
     *
     * @param $version
     * @param $encoding
     * @param $format_output
     */
    public static function init(
        $version = "1.0",
        $encoding = "UTF-8",
        $format_output = true
    )
    {
        self::$xml = new DOMDocument($version, $encoding);
        self::$xml->formatOutput = $format_output;
        self::$encoding = $encoding;
    }

    /*
     * Get the root XML node, if there isn't one, create it.
     */

    /**
     * Convert an Array to XML
     *
     * @param mixed $node - XML as a string or as an object of DOMDocument
     *
     * @return mixed
     */
    private static function &convert($node)
    {
        $output = [];

        switch ($node->nodeType) {
            case XML_CDATA_SECTION_NODE:
                $output["@cdata"] = trim($node->textContent);
                break;

            case XML_TEXT_NODE:
                $output = trim($node->textContent);
                break;

            case XML_ELEMENT_NODE:
                // for each child node, call the covert function recursively
                for ($i = 0, $m = $node->childNodes->length; $i < $m; $i++) {
                    $child = $node->childNodes->item($i);
                    $v = self::convert($child);
                    if (isset($child->tagName)) {
                        $t = $child->tagName;

                        // assume more nodes of same kind are coming
                        if (!isset($output[$t])) {
                            $output[$t] = [];
                        }
                        $output[$t][] = $v;
                    } else {
                        //check if it is not an empty text node
                        if ($v !== "") {
                            $output = $v;
                        }
                    }
                }

                if (is_array($output)) {
                    // if only one node of its kind, assign it directly instead if array($value);
                    foreach ($output as $t => $v) {
                        if (is_array($v) && count($v) == 1) {
                            $output[$t] = $v[0];
                        }
                    }
                    if (empty($output)) {
                        //for empty nodes
                        $output = "";
                    }
                }

                // loop through the attributes and collect them
                if ($node->attributes->length) {
                    $a = [];
                    foreach ($node->attributes as $attrName => $attrNode) {
                        $a[$attrName] = (string)$attrNode->value;
                    }
                    // if its an leaf node, store the value in @value instead of directly storing it.
                    if (!is_array($output)) {
                        $output = ["@value" => $output];
                    }
                    $output["@attributes"] = $a;
                }
                break;
        }

        return $output;
    }
}

function redirectionUrl ($stage) {

    if (!empty($stage)) {

        switch ($stage) {
            case "Quote":
                $redirectionUrl = "quote_url";
                break;
            case "Rider":
                $redirectionUrl = "quote_url";
                break;
            case "Proposal Pending":
                $redirectionUrl = "proposal_url";

                break;
            case "Payment Pending":
                $redirectionUrl = "proposal_url";

                break;
            case "Issued":
                $redirectionUrl = "proposal_url";

                break;
            case "Inception":
                $redirectionUrl = "proposal_url";

                break;
            default:
                $redirectionUrl = "quote_url";
        }
    } else {
        $redirectionUrl = "quote_url";
    }

    return $redirectionUrl;


}

function subStageTostage($stage){
        $subStageId = substagemaster::where('sub_stage_name', $stage)->pluck('id')->first();
        $stageName = StagemasterModel::whereRaw('FIND_IN_SET(?, sub_stage_name)', [$subStageId])->pluck('stage_name')->first();
        return $stageName;
}

function StageToSubStage($stage) {
    $sub_stage_name = [];
    if (!is_array($stage)) {
        $stage = [$stage];
    }
    $results = StagemasterModel::select('stage_master.id', 'stage_master.stage_name', 'sub_stage_master.sub_stage_name')
    ->join('sub_stage_master', DB::raw('FIND_IN_SET(sub_stage_master.id, stage_master.sub_stage_name) > 0'), '>', DB::raw('0'))
        ->whereIn('stage_master.stage_name', $stage)
        ->get();
    foreach ($results as $result) {
        $sub_stage_name[] = $result->sub_stage_name;
    }
   return  $sub_stage_name;
}

if (!function_exists('EmailActivityLog')) {
    function EmailActivityLog($user, $otp, $expiry,$subject = null,$body = null,$email = null)
    {
        $userId = $user->id;
        $type   = 'General';
        if($otp != null){
            $subject = 'OTP Sent';
            $body    = "Your OTP is " . $otp . " and it expires at " . $expiry;
            $type = 'OTP';
            $email = $user->email;
        }
        // Log email activity
        EmailActivityLog::create([
            'user_id' => $userId,
            'email' => credential_decrypt($email??$user->email),
            'subject' => $subject,
            'body' => $body,
            'type' => $type,
            'status' => 'Email Sent',
            'sent_at' => now(),
        ]);

        return true;
    }
}

if (!function_exists('sendCron')) {
    function sendCron() {

        echo "Hello from sendCron!";
    }
}

if (!function_exists('SMSlogActivity')) {

    function SMSlogActivity($user,$template,$smsStatus)
    {
        $userId = $user->id;
        if (isset($user->mobile_number)) {
            SmsActivityLog::create([
                'user_id' => $userId,
                'mobile' => $user->mobile_number,
                'message' => $template,
                'type' => 'OTP',
                'status' => $smsStatus,
                'sent_at' => now(),
            ]);
        }
    }
}

if(!function_exists('ExcelDataExportLog'))
{
    function ExcelDataExportLog($user_id,$filepath,$source,$status,$request)
    {
        
        $dataExportLogData=DataExportLog::create([
            'user_id' => $user_id,
            'file' => $filepath,
            'source' => $source,
            'status' => $status,
            'request' => json_encode([$request]),
            'file_expiry' => now()->addDays(1),
            'uid' => getUUID()
        ]);
        return $dataExportLogData;
        

        
    }
}
function ql()
    {
        return \DB::enableQueryLog();
    }
    function gql()
    {
        return \DB::getQueryLog();
    }

    function assignLobs($userId)
    {
        $lobs = lobMaster::where('is_enabled', 'Y')->pluck('id');
    
        if ($lobs->isEmpty()) {
            throw new \Exception('Lob Not Enabled');
        }
    
        foreach ($lobs as $lobId) {
            DB::table('user_lob_relation')->insert([
                'user_id' => $userId,
                'lob_id'  => $lobId
            ]);
        }
    }

if (!function_exists('maskMobile')) {
    function maskMobile($mobile, $maskChar = 'X', $visibleStart = 2, $visibleEnd = 2)
    {
        if (empty($mobile)) {
            return $mobile;
        }
        
        $length = strlen($mobile);
        $visibleLength = $visibleStart + $visibleEnd;
        
        if ($length <= $visibleLength) {
            return $mobile;
        }
        
        $maskedLength = $length - $visibleLength;
        
        return substr($mobile, 0, $visibleStart) . 
               str_repeat($maskChar, $maskedLength) . 
               substr($mobile, -$visibleEnd);
    }
}
if (!function_exists('mis_build_replace_map')) {

    function mis_build_replace_map()
    {
        static $map = null;

        if ($map !== null) {
            return $map;
        }

        $map = [];

        $rows = MisColumnView::select('mongo_key', 'existing_value', 'new_value')->get();

        foreach ($rows as $r) {
            $k = normalize_key($r->mongo_key);
            $v = normalize_value($r->existing_value);

            if (!isset($map[$k])) {
                $map[$k] = [];
            }

            $map[$k][$v] = $r->new_value;
        }

        return $map;
    }
}

if (!function_exists('mis_replace_single_value')) {
    function mis_replace_single_value($key, $value)
    {
        if ($value === null || $value === '') {
            return $value;
        }

        $map = mis_build_replace_map();

        $normKey = normalize_key($key);
        $normVal = normalize_value($value);

        if (isset($map[$normKey][$normVal])) {
            return $map[$normKey][$normVal]; 
        }

        return $value;
    }
}

if (!function_exists('mis_replace_values')) {

    function mis_replace_values($data)
    {
        $map = mis_build_replace_map();

        $arr = json_decode(json_encode($data), true);

        $replaceRecursively = function (&$node) use (&$map, &$replaceRecursively) {
            if (!is_array($node)) return;

            foreach ($node as $k => &$v) {
                $normKey = normalize_key($k);

                if (is_array($v)) {
                    $replaceRecursively($v);
                } else {
                    $normVal = normalize_value($v);
                    if (isset($map[$normKey][$normVal])) {
                        $v = $map[$normKey][$normVal];
                    }
                }
            }
            unset($v);
        };

        $replaceRecursively($arr);

        return $arr;
    }
}

if (!function_exists('normalize_key')) {
    function normalize_key($key)
    {
        if ($key === null) return '';
        $k = (string)$key;
        $k = preg_replace('/[\s\-\/\\\\]+/', '_', $k);
        $k = preg_replace('/_+/', '_', $k);
        $k = trim($k, "_ \t\n\r\0\x0B");
        $k = strtolower($k);
        return $k;
    }
}

if (!function_exists('normalize_value')) {
    function normalize_value($val)
    {
        if ($val === null) return '';
        if (is_array($val) || is_object($val)) {
            return '__NON_SCALAR__';
        }
        $s = (string)$val;
        $s = trim($s);
        $s = strtolower($s);
        return $s;
    }
}

if (!function_exists('get_full_name')) {
    function get_full_name($user)
    {
        if (!$user) return null;

        $first  = $user->name ? credential_decrypt($user->name) : '';
        $middle = $user->middle_name ? credential_decrypt($user->middle_name) : '';
        $last   = $user->last_name ? credential_decrypt($user->last_name) : '';

        return trim("$first $middle $last");
    }
}

if (!function_exists('mis_reporting_data')) {

    function mis_reporting_data(array $data, array $MisColumnName)
    {
        if (empty($data)) {
            return $data;
        }

        $sellerMobiles = [];
        foreach ($data as $row) {
            if (isset($row['seller_mobile']) && !empty($row['seller_mobile'])) {
                $sellerMobiles[] = credential_encrypt($row['seller_mobile']);
            }
        }
        
        if (empty($sellerMobiles)) {
            return $data;
        }
        
        $sellerMobiles = array_unique($sellerMobiles);

        $users = User::whereIn('mobile', $sellerMobiles)->get();
        
        $userByEncryptedMobile = [];
        $supervisorIds = [];      
        $rmEmployeeCodes = [];    
        $sellerUserIds = [];      
        
        foreach ($users as $user) {
            $userByEncryptedMobile[$user->mobile] = $user;
            $sellerUserIds[] = $user->id;
            
            if (!empty($user->reportingto)) {
                $supervisorIds[] = $user->reportingto;
            }
            
            if ($user->usertype != 1 && !empty($user->employee_code)) {
                $rmEmployeeCodes[] = $user->employee_code;
            }
        }
        
        $supervisors = [];
        if (!empty($supervisorIds)) {
            $supervisorIds = array_unique($supervisorIds);
            $supervisorUsers = User::whereIn('id', $supervisorIds)->get();
            foreach ($supervisorUsers as $sup) {
                $supervisors[$sup->id] = $sup;
            }
        }

        $rms = [];
        if (!empty($rmEmployeeCodes)) {
            $rmEmployeeCodes = array_unique($rmEmployeeCodes);
            $rmUsers = User::whereIn('employee_code', $rmEmployeeCodes)
                ->whereNotIn('id', $sellerUserIds)
                ->get();
            foreach ($rmUsers as $rm) {
                $rms[$rm->employee_code] = $rm;
            }
        }
        
        foreach ($data as $index => $row) {
            if (!isset($row['seller_mobile'])) {
                continue;
            }

            $sellerMobile = credential_encrypt($row['seller_mobile']);
            $details = $userByEncryptedMobile[$sellerMobile] ?? null;
            
            if (!$details) {
                $emptyFields = [
                    'rm_name'           => null,
                    'rm_mobile'         => null,
                    'rm_code'           => null,
                    'rm_email'          => null,
                    'pos_code'          => null,
                    'supervisor_name'   => null,
                    'supervisor_mobile' => null,
                    'supervisor_email'  => null,
                ];
                
                foreach ($emptyFields as $key => $value) {
                    if (in_array($key, $MisColumnName)) {
                        $data[$index][$key] = $value;
                    }
                }
                continue;
            }
            
            if ($details->usertype == 1) {
                $rm = null;
                if (!empty($details->reportingto)) {
                    $rm = $supervisors[$details->reportingto] ?? null;
                }
                
                $rmData = [
                    'rm_name'           => $rm ? get_full_name($rm) : null,
                    'rm_mobile'         => $rm ? credential_decrypt($rm->mobile) : null,
                    'rm_email'          => $rm ? credential_decrypt($rm->email) : null,
                    'rm_code'           => $rm ? $rm->employee_code : null,   
                    'pos_code'          => $details->pos_code ?? null,    
                    'supervisor_name'   => null,
                    'supervisor_mobile' => null,
                    'supervisor_email'  => null,
                ];
                
                foreach ($rmData as $key => $value) {
                    if (in_array($key, $MisColumnName)) {
                        $data[$index][$key] = $value;
                    }
                }
                continue;
            }
    
            $rm = null;
            if (!empty($details->employee_code)) {
                $rm = $rms[$details->employee_code] ?? null;
            }
            
            $supervisor = null;
            if (!empty($details->reportingto)) {
                $supervisor = $supervisors[$details->reportingto] ?? null;
            }
            
            $rmData = [
                'rm_name'           => $rm ? get_full_name($rm) : null,          
                'rm_mobile'         => $rm ? credential_decrypt($rm->mobile) : null, 
                'rm_email'          => $rm ? credential_decrypt($rm->email) : null,  
                'rm_code'           => $details->employee_code ?? null,           
                'pos_code'          => $details->pos_code ?? null,                
                'supervisor_name'   => $supervisor ? get_full_name($supervisor) : null,   
                'supervisor_mobile' => $supervisor ? credential_decrypt($supervisor->mobile) : null,
                'supervisor_email'  => $supervisor ? credential_decrypt($supervisor->email) : null,
            ];
            
            foreach ($rmData as $key => $value) {
                if (in_array($key, $MisColumnName)) {
                    $data[$index][$key] = $value;
                }
            }
        }

        return $data;
    }
}

if (!function_exists('mis_customer_renewal_popup')) {

    function mis_customer_renewal_popup(array $data, $startDate, $endDate, $MisColumnName): array      
        {
            if (!in_array('renewal_customer_name', $MisColumnName)) {
                return [];
            }
            $users = Customer::join('customer_policy_expire','customers.id','=','customer_id')
                    ->select('customers.id','customers.name','customers.email','customers.mobile','customer_policy_expire.mobile_no as mobile_no_entered','customer_policy_expire.policy_no as registration_no','customer_policy_expire.policy_end_date')
                    ->whereBetween('customer_policy_expire.created_at', [$startDate,$endDate])->get();
            $data = [];
            return $users->map(function ($user) {
                return [
                    'renewal_customer_name' => credential_decrypt($user->name) ?? null,
                    'renewal_customer_mobile_no' => $user->mobile_no_entered ?? null,
                    'customer_mobile_no' => credential_decrypt($user->mobile) ?? null,
                    'renewal_customer_registration_no' => $user->registration_no ?? null,
                    'renewal_customer_policy_end_date' => $user->policy_end_date ?? null,
                    'renewal_customer_email_id' => credential_decrypt($user->email) ?? null,
                ];
            })->toArray();
        }
    }

if (!function_exists('ippb_decrypt_sso_payload')) {
function ippb_decrypt_sso_payload(string $encryptedData)
{
    $secretKey = config('FT_KEY', 'Dt4563Hjkgtpk&6jhylkcFtyM3TyP08H');
    // $secretKey = substr(config('ippb.sso_encryption_key', 'CHAN91D6CDA4042AFDD292EB03E84B2BALC'), 3);

    // Extract IV (last 16 chars)
    $iv = substr($encryptedData, -16);
    $cipherBase64 = substr($encryptedData, 0, -16);

    $cipherRaw = base64_decode($cipherBase64, true);
    if ($cipherRaw === false) {
        throw new \Exception('Base64 decode failed');
    }

    $plainText = openssl_decrypt(
        $cipherRaw,
        'aes-256-gcm',
        $secretKey,
        OPENSSL_RAW_DATA,
        $iv
    );

    if ($plainText === false) {
        throw new \Exception('Decrypt failed');
    }

    return $plainText;
}
}

if (!function_exists('ippb_decrypt_sso_payload_old')) {

    function ippb_decrypt_sso_payload_old(string $encryptedData)
    {
        try {
                $IPPB_SSO_ENCRYPTION_KEY = config('FT_KEY', 'Dt4563Hjkgtpk&6jhylkcFtyM3TyP08H');
                $secret                  = $IPPB_SSO_ENCRYPTION_KEY;
                $key                     = hash('sha256', $secret);
                $ivLength                = 16;

                $secret_iv     = substr($encryptedData, -$ivLength);
                $iv            = substr(hash('sha256', $secret_iv), 0, 16);
                $encryp_string = substr($encryptedData, 0, -$ivLength);

                $decoded = base64_decode($encryp_string, true);
                if ($decoded === false) {
                    throw new \Exception('Base64 decode failed');
                }

                $plainText = openssl_decrypt($decoded, 'AES-256-CBC', $key, 0, $iv);
                if ($plainText === false) {
                    throw new \Exception('Decrypt failed');
                }

                return trim($plainText);
            } catch (\Throwable $e) {
                \Log::error("ippb decrypt_sso_payload error: " . $e->getMessage());
                return false;
            }

    }

}

if (!function_exists('ippb_encrypt_sso_payload')) {
function ippb_encrypt_sso_payload(string $plainText)
{
    $secretKey = config('FT_KEY', 'Dt4563Hjkgtpk&6jhylkcFtyM3TyP08H');
    // $secretKey = substr(config('ippb.sso_encryption_key', 'CHAN91D6CDA4042AFDD292EB03E84B2BALC'), 3);

    $iv = Str::random(16);

    $cipherText = openssl_encrypt(
        $plainText,
        'aes-256-gcm',
        $secretKey,
        OPENSSL_RAW_DATA,
        $iv
    );

    if ($cipherText === false) {
        throw new \Exception('Encrypt failed');
    }

    return base64_encode($cipherText) . $iv;
}
}

if (!function_exists('ippb_encrypt_sso_payload_old')) {

    function ippb_encrypt_sso_payload_old(string $plainText)
    {
        try {
            $IPPB_SSO_ENCRYPTION_KEY = config('FT_KEY', 'Dt4563Hjkgtpk&6jhylkcFtyM3TyP08H');
            $secret                  = $IPPB_SSO_ENCRYPTION_KEY;
            $key                     = hash('sha256', $secret);

            $secret_iv = bin2hex(random_bytes(8));
            $iv        = substr(hash('sha256', $secret_iv), 0, 16);

            $cipher = openssl_encrypt($plainText, 'AES-256-CBC', $key, 0, $iv);
            if ($cipher === false) {
                throw new \Exception('Encrypt failed');
            }

            return base64_encode($cipher) . $secret_iv;
        } catch (\Throwable $e) {
            \Log::error("ippb encrypt_sso_payload error: " . $e->getMessage());
            return false;
        }
    }



}

if (!function_exists('ippb_encrypted_error_response')) {

    function ippb_encrypted_error_response(string $message, int $statusCode = 500)
    {
        try {
            $errorPayload = [
                "app_response" => [
                    "timestamp" => now()->toDateTimeString(),
                    "status" => "failure",
                    "error_details" => [
                        "error_reason" => $message,
                        "other_1" => "",
                        "other_2" => "",
                        "other_3" => "",
                    ]
                ]
            ];

            $encrypted = ippb_encrypt_payload_sso(json_encode($errorPayload),config('FT_KEY'));

            if ($encrypted === false) {
                throw new \Exception('Error payload encryption failed');
            }

            return response()->json([
                'response_data' => $encrypted
            ], $statusCode);

        } catch (\Throwable $e) {
            \Log::error("ippb_encrypted_error_response error: " . $e->getMessage());

            return response()->json([
                'message' => 'Internal error'
            ], 500);
        }
    }
}
if (! function_exists('token_verify_bcl')) {

    function token_verify_bcl(string $token, string $flag1)
    {
        $url = config('bcl_sso_verify_token_url');

        $queryParams = [
            'Token' => $token,
            'Flag1' => $flag1,
        ];

        try {
            $response = Http::withHeaders([
                    'Accept'     => '*/*',
                    'User-Agent' => 'curl/7.79.1',
                ])
                ->withoutVerifying()   
                ->timeout(30)
                ->get($url, $queryParams);

            Log::error('token_verify_request', [
                'url' => $url,
                'params' => $queryParams,
            ]);

            Log::error('token_verify_response', [
                'response' => $response->json(),
            ]);

            return $response->json();

        } catch (\Exception $e) {

            Log::error('token_verify_error', [
                'message' => $e->getMessage(),
            ]);

            return [
                'status'  => false,
                'message' => 'Request Error: ' . $e->getMessage(),
            ];
        }
    }
}

if (!function_exists('decrypt_payload_ippb')) {
    function decrypt_payload_ippb(string $encryptedData): string
{
    $decKey = config('IPPB_KEY','CHAN91D6CDA4042AFDD292EB03E84B2BALC');

    // Match Java key logic
    if (strlen($decKey) === 35) {
        $decKey = substr($decKey, 3);
    }

    if (strlen($decKey) !== 32) {
        throw new Exception('Invalid Key Found. Key should be exactly 32 bytes');
    }

    // Java uses ZERO IV
    $iv = str_repeat("\0", 16);

    $cipherRaw = base64_decode($encryptedData, true);
    if ($cipherRaw === false) {
        throw new Exception('Base64 decode failed');
    }

    $plainText = openssl_decrypt(
        $cipherRaw,
        'aes-256-gcm',
        $decKey,
        OPENSSL_RAW_DATA,
        $iv
    );

    if ($plainText === false) {
        throw new Exception('Decrypt failed');
    }

    return $plainText;
}

}

if (!function_exists('encrypt_payload_ippb')) {
    function encrypt_payload_ippb(string $plainText, $encKey='CHAN91D6CDA4042AFDD292EB03E84B2BALC'): string
{
    // $encKey = config('ippb.sso_encryption_key_ippb','CHAN91D6CDA4042AFDD292EB03E84B2BALC');

    // Match Java logic
    if (strlen($encKey) === 35) {
        $encKey = substr($encKey, 3);
    }

    if (strlen($encKey) !== 32) {
        throw new Exception('Invalid Key Found. Key should be exactly 32 bytes');
    }

    // ZERO IV (16 bytes)
    $iv = str_repeat("\0", 16);

    $cipherText = openssl_encrypt(
        $plainText,
        'AES-256-CBC',
        $encKey,
        OPENSSL_RAW_DATA,
        $iv
    );

    if ($cipherText === false) {
        throw new Exception('Encrypt failed');
    }

    // Java returns only Base64(cipherText)
    return base64_encode($cipherText);
}

}

if (!function_exists('generate_ippb_random_number')) {
    function generate_ippb_random_number()
    {
        return 'IPB' . bin2hex(random_bytes(16));
    }
}

function getSecretKey(string $secret): string
{
    return hash('sha256', $secret, true); 
}


    if (!function_exists('ippb_encrypt_payload_sso')) {
    function ippb_encrypt_payload_sso(string $plainText, ?string $secret = 'CHAN91D6CDA4042AFDD292EB03E84B2BALC'): string
    {

        $iv  = random_bytes(12); // IV_LENGTH = 12
        $key = getSecretKey($secret);
        $tag = '';

        $cipherText = openssl_encrypt(
            $plainText,
            'aes-256-gcm',
            $key,
            OPENSSL_RAW_DATA,
            $iv,
            $tag,
            '',
            16 // TAG_LENGTH
        );

        if ($cipherText === false) {
            throw new RuntimeException('AES-GCM Encryption failed');
        }

        return base64_encode($iv . $cipherText . $tag);
    }
}


if (!function_exists('ippb_decrypt_payload_sso')) {
    function ippb_decrypt_payload_sso(string $encryptedText , ?string $secret = 'CHAN91D6CDA4042AFDD292EB03E84B2BALC'): string
    { 
        $decoded = base64_decode($encryptedText, true);
        if ($decoded === false) {
            throw new RuntimeException('Invalid Base64 data');
        }

        $iv         = substr($decoded, 0, 12);
        $tag        = substr($decoded, -16);
        $cipherText = substr($decoded, 12, -16);

        $key = getSecretKey($secret);

        $plainText = openssl_decrypt(
            $cipherText,
            'aes-256-gcm',
            $key,
            OPENSSL_RAW_DATA,
            $iv,
            $tag
        );
        if ($plainText === false) {
            throw new RuntimeException('AES-GCM Decryption failed');
        }
        
        return $plainText;
    }
}



if (!function_exists('buildHierarchyMaps')) {
    function buildHierarchyMaps()
    {
        $users = User::query()
            ->select('id', 'name', 'employee_code','mobile', 'usertype', 'reportingTo', 'status')
            ->where('status', 'Y')
            ->get();

        $usersById = [];
        $sameTypeChildrenMap = [];
        $employeeCodeMap = [];

        foreach ($users as $user) {
            $usersById[$user->id] = $user;

            // Same usertype mapping via reportingTo
            if (!empty($user->reportingTo)) {
                $sameTypeChildrenMap[$user->reportingTo][] = $user->id;
            }

            // Group users by employee_code for different usertype logic for users other than Employee
            if (!empty($user->employee_code) && !in_array($user->usertype, [1,7])) {
                $employeeCodeMap[$user->employee_code][] = $user->id;
            }
        }

        return [
            'usersById' => $usersById,
            'sameTypeChildrenMap' => $sameTypeChildrenMap,
            'employeeCodeMap' => $employeeCodeMap,
        ];
    }
}

if (!function_exists('getDirectChildrenFromMap')) {
    function getDirectChildrenFromMap($parentUser, $usersById, $sameTypeChildrenMap, $employeeCodeMap)
    {
        $childIds = [];

        /**
         * SAME usertype -> reportingTo
         */
        if (isset($sameTypeChildrenMap[$parentUser->id])) {
            foreach ($sameTypeChildrenMap[$parentUser->id] as $childId) {
                if (isset($usersById[$childId])) {
                    $child = $usersById[$childId];

                    if (in_array($child->usertype,[1,7])) {
                        $childIds[] = $childId;
                    }
                }
            }
        }

        /**
         * DIFFERENT usertype -> employee_code
         */
        if (!empty($parentUser->employee_code) && isset($employeeCodeMap[$parentUser->employee_code])) {
            foreach ($employeeCodeMap[$parentUser->employee_code] as $childId) {
                if (isset($usersById[$childId])) {
                    $child = $usersById[$childId];

                    if ((int)$child->usertype !== (int)$parentUser->usertype && (int)$child->id !== (int)$parentUser->id) {
                        $childIds[] = $childId;
                    }
                }
            }
        }
        $childIds[] = $parentUser->id;
        return array_values(array_unique($childIds));
    }
}

if (!function_exists('getFullDownlineIdsFromMap')) {
    function getFullDownlineIdsFromMap($user, $usersById, $sameTypeChildrenMap, $employeeCodeMap)
    {
        $result = [];
        $visited = [];

        $stack = [(int) $user->id];

        while (!empty($stack)) {
            $currentId = array_pop($stack);

            if (isset($visited[$currentId])) {
                continue;
            }

            $visited[$currentId] = true;

            $currentUser = $usersById[$currentId] ?? null;
            if (!$currentUser) {
                continue;
            }

            /**
             * 1. Same usertype children via reportingTo
             */
            $sameTypeChildren = $sameTypeChildrenMap[$currentId] ?? [];

            foreach ($sameTypeChildren as $childId) {
                if (!isset($visited[$childId])) {
                    $result[] = (int) $childId;
                    $stack[] = (int) $childId;
                }
            }

            /**
             * 2. Cross usertype mapping via employee_code
             * IMPORTANT: only fetch exact mapped child nodes, not all same-code siblings repeatedly
             */
            $employeeCode = $currentUser->employee_code ?? null;

            if (!empty($employeeCode) && isset($employeeCodeMap[$employeeCode])) {
                foreach ($employeeCodeMap[$employeeCode] as $mappedUserId) {
                    if ((int)$mappedUserId === (int)$currentId) {
                        continue;
                    }

                    if (!isset($visited[$mappedUserId])) {
                        $result[] = (int) $mappedUserId;
                        $stack[] = (int) $mappedUserId;
                    }
                }
            }
        }

        return array_values(array_unique($result));
    }
}

if (!function_exists('getDirectMappedUsersFromMap')) {
    function getDirectMappedUsersFromMap($loginUser, $usersById, $sameTypeChildrenMap, $employeeCodeMap, $targetUsertype = null)
    {
        $directChildIds = getDirectChildrenFromMap(
            $loginUser,
            $usersById,
            $sameTypeChildrenMap,
            $employeeCodeMap
        );

        $directUsers = collect($directChildIds)
            ->map(fn($id) => $usersById[$id] ?? null)
            ->filter();

        if (!empty($targetUsertype)) {
            $directUsers = $directUsers->filter(fn($user) => (int)$user->usertype === (int)$targetUsertype);
        }

        return $directUsers->values();
    }

}
    if (!function_exists('fullMaskValue')) {
        function fullMaskValue($value)
        {
            $value = str_replace('*', 'X', $value);
            return preg_replace('/[A-Za-z0-9*]/', 'X', $value);        
        }
    }

    if (!function_exists('partialMaskValue')) {
        function partialMaskValue($value, $type)
        {
            $value = str_replace('*', 'X', $value);

            switch ($type) {

                case 'pan_no':
                    // ABCDE1234F → XXXXX1234X
                    return 'XXXXX' . substr($value, 5, 4) . 'X';


                //  MOBILE 
                case 'primary_insured_mobile':
                case 'proposer_mobile':
                case 'seller_mobile':
                case 'seller_username':
                    // 9876543210 → 9XXXXXX210
                    return substr($value, 0, 1)
                        . str_repeat('X', max(strlen($value) - 4, 0))
                        . substr($value, -3);


                //  EMAIL 
                case 'primary_insured_emailid':
                case 'proposer_emailid':
                case 'seller_email':

                    if (!empty($value) && strpos($value, '@') !== false) {
                        [$name, $domain] = explode('@', $value);

                        return substr($name, 0, 1)
                            . str_repeat('X', max(strlen($name) - 2, 1))
                            . substr($name, -1)
                            . '@' . $domain;
                    }
                    return $value;


                //DOB 
                case 'nominee_dob':
                case 'primary_insured_dob':
                case 'proposer_dob':
                    // 15-08-1995 → XX-XX-1995
                    return 'XX-XX-' . substr($value, -4);


                //  AADHAAR 
                case 'addhar_no':

                    if (!empty($value)) {
                        $clean = preg_replace('/\D/', '', $value);

                        if (strlen($clean) >= 4) {
                            return 'XXXX XXXX ' . substr($clean, -4);
                        }
                    }
                    return $value;


                //  NAME 
                case 'nominee_relationship':
                case 'first_name':
                case 'last_name':
                case 'nominee_name':
                case 'primary_insured_name':
                case 'proposer_name':
                case 'seller_name':
                case 'Alphabetic':

                    return collect(explode(' ', $value))->map(function ($word) {
                        return substr($word, 0, 1)
                            . str_repeat('X', max(strlen($word) - 1, 1));
                    })->implode(' ');


                //  ADDRESS 

                case 'address_line_1':
                case 'address_line_2':
                case 'address_line_3':

                    return preg_replace_callback('/[A-Za-z0-9*]+/', function ($match) {

                        $word = $match[0];
                        $len  = strlen($word);

                        if ($len <= 2) {
                            return str_repeat('X', $len);
                        }

                        if ($len == 3) {
                            return 'XX' . substr($word, -1);
                        }

                        $start = substr($word, 0, 2);
                        $end   = substr($word, -1);

                        return $start . str_repeat('X', $len - 3) . $end;

                    }, $value);

                default:
                    return preg_replace('/[A-Za-z0-9*]/', 'X', $value);
            }
        }
    }

    if (!function_exists('applyMasking')) {

    function applyMasking($rows, $scope = 'frontend')
    {
        $user = Auth::user();
        $rows = collect($rows)->map(function ($row) {
            return is_object($row) && method_exists($row, 'toArray')
                ? $row->toArray()
                : (array) $row;
        })->values()->toArray();

        $roleIds = $user->roles->pluck('id')->toArray(); 
        $routePath = request()->path();

        $moduleName = null;

        if (str_contains($routePath, 'mis_report_Data')) {
            $moduleName = 'MIS Reports';
        } elseif (str_contains($routePath, 'policystatus')) {
            $moduleName = 'Policy Status';
        }
        $moduleId = DB::table('mask_configuration_master')
            ->where('status', 'Y')
            ->where('usertype', $user->usertype)
            ->whereIn('role', $roleIds)
            ->when($moduleName, function ($q) use ($moduleName) {
                $q->where('module_name', $moduleName);
            })
            ->value('id');

        $maskConfigs = DB::table('role_pi_data_mapping')
            ->where('module_id', $moduleId)
            ->where('is_enabled', 'Y')
            ->where(function ($q) use ($scope) {
                if ($scope =='excel') {
                    $q->whereIn('mask_scope', ['Excel Only', 'Frontend & Excel']);
                } else {
                    $q->whereIn('mask_scope', ['Frontend Only', 'Frontend & Excel']);
                }
            })
            ->get()
            ->mapWithKeys(function ($item) {
                return [
                    strtolower(trim(str_replace([' ', '.'], '_', $item->field_name))) => $item
                ];
            });

        foreach ($rows as $rowIndex => $row) {
            foreach ($row as $field => $value) {

                $normalizedField = strtolower(trim(str_replace([' ', '.'], '_', $field)));

                if (!isset($maskConfigs[$normalizedField])) continue;
                if (!isset($value) || trim((string)$value) === '') continue;

                $config = $maskConfigs[$normalizedField];

                $maskType = strtolower(trim($config->mask_type));
                $formula  = strtolower(trim(str_replace(' ', '_', $config->mask_formula)));

                $value = is_scalar($value) ? (string)$value : json_encode($value);

                if ($maskType === 'full masking') {
                    $rows[$rowIndex][$field] = fullMaskValue($value);
                } elseif ($maskType === 'partial masking') {
                    $rows[$rowIndex][$field] = partialMaskValue($value, $formula);
                }
            }
        }

        return $rows;
}
}