<?php

namespace App\Http\Controllers;

use App\Models\PartnerUserMapping;
use App\Models\ThemeMaster;
use App\Models\UserAdditionalData;
use App\Models\UserMapping;
use Exception;
use App\Models\User;
use App\Models\Broker;
use App\Models\lobMaster;
use App\Models\userTypes;
use App\Models\TokenModel;
use Illuminate\Support\Str;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Auth;
use App\Models\SSO;
use Carbon\Carbon;
use App\Models\Customer; 
use App\Models\masterCompany;
 

class TokenController extends BaseController
{
    public $AuthUser;
    public function __construct(Auth $auth)
    {
        $this->AuthUser = $auth::user();
    }
    public function generateToken(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $checkUserLobRelation = true;
        if(config('Check_user_lob_relation')==0){
            $checkUserLobRelation = false;
        }

        if (!$request->has('user_id') && $checkUserLobRelation) {
            $userLobs = DB::table('user_lob_relation')->where('user_id', $this->AuthUser->id)->where('deleted_at',null)->pluck('lob_id')->toArray();

            if (!in_array($request->lob_id, $userLobs)) {
                return response()->json([
                    'status' => 403,
                    'return_data' => [],
                    'message' => 'You are not authorized to access this LOB'
                ], 403);
            }
        }
        
        $posUser = credential_decrypt($request->user_id);

        if(!empty($posUser) && $checkUserLobRelation) {
            $userLobs = DB::table('user_lob_relation')->where('user_id', $posUser)->where('deleted_at',null)->pluck('lob_id')->toArray();

            if (!in_array($request->lob_id, $userLobs)) {
                return response()->json([
                    'status' => 403,
                    'return_data' => [],
                    'message' => 'You are not authorized to access this LOB'
                ], 403);
            }
        } 
        
        $save_business_fields = false;
        if(config('ANG.Validation')=="true") {

            $business_type = $request->business_type ?? null;
            $business_code = $request->business_code ?? null;
            $channel = $request->channel ?? null;
            
    
            if (!empty($channel) && $channel == "ANG") {
    
                if (!empty($business_code)) {
        
                    $check = DB::table('employee_payroll_id')
                        ->where('user_name', $business_code)
                        ->first();
        
                    if ($check) {
                        $save_business_fields = true;
                    } else {
                        return response()->json([
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'Invalid business_code'
                        ], 500);
                    }
                }
            
            }
            else
            {
                if (!empty($business_code) && !empty($business_type)) {
                    $save_business_fields = true;
                }
            }
        }

        $lobList = lobMaster::select('id', 'lob')->where('is_enabled', 'Y')->get();
        $motorlobarr = ['CAR', 'GCV', 'PCV', 'BIKE', 'MISC'];
        $param = '';
        foreach ($lobList as $key => $value) {
            if (in_array($value->lob, $motorlobarr) && $request->lob_id == $value->id) {
                $param = '?xutm=';
                break;
            } else {
                $param = '?token=';
            }
        }

        // dd($posUser,Auth::user());
           if(empty($posUser))
           {
            $user = Auth::user();

           }else{
            $user = User::where('id',$posUser)->first();
           }

            if (!$user) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'No Data Found'
                ], 500);
            }

            $users = DB::table('users')
                ->when($user->usertype != 0, function ($query) {
                    return $query->join('usertypes', 'usertypes.id', '=', 'users.usertype');
                })
                ->where('users.id', $user->id)
                ->first();

            $lobList = lobMaster::select('id', 'lob')->where('is_enabled', 'Y')->get();
            $motorlobarr = ['CAR', 'GCV', 'PCV', 'BIKE', 'MISC'];
            $param = '';
            foreach ($lobList as $key => $value) {
                if (in_array($value->lob, $motorlobarr) && $request->lob_id == $value->id) {
                    $param = '?xutm=';
                    break;
                } else {
                    $param = '?token=';
                }
            }
            $token = $request->bearerToken();

            $insert = TokenModel::updateOrCreate(
                ['token' => $token],
                [
                    'seller_id'   => $user->id,
                    'seller_type' => getUserTypeIdentifier($user->usertype),
                    'xutm'        => Str::uuid(),
                    'lob_id'      => $request->lob_id,
                ]
            );

            if ($save_business_fields) {
                $insert->business_type = $business_type;
                $insert->business_code = $business_code;
            }

            $insert->save();

            if ($insert) {
                $token = TokenModel::join('lob_master', 'lob_master.id', 'journey_api_token.lob_id')
                    ->where('xutm', $insert->xutm)
                    ->first();
                    $token = TokenModel::join('lob_master', 'lob_master.id', 'journey_api_token.lob_id')
                    ->where('xutm', $insert->xutm)
                    ->first();
                if(getUserTypeIdentifier($user->usertype)=='U'){
                    $separator = str_contains($token->customer_frontend_url, '?') ? '&' : '?';
                    $frontend_url = $token->customer_frontend_url;
                }else{
                    $separator = str_contains($token->frontend_url, '?') ? '&' : '?';
                    $frontend_url = $token->frontend_url;
                }
    
                $response = [
                    'status' => 200,
                    'return_data' => [        
                        'frontend_url' => $frontend_url . str_replace('?', $separator, $param) . $token->xutm,
                        'redirect_insame_tab' => (int)config('redirect_insame_tab',0)
                    ],
                    'message' => 'Data Inserted successfully'
                ];

                logApiRequestResponse(
                    'Generate Token' . '<br>' . 'LOB = ' . $lobList->firstWhere('id', $insert->lob_id)?->lob,
                    'POST',
                    'LOB = ' . $lobList->firstWhere('id', $request->lob_id)?->lob,
                    $response,
                    200,
                    '',
                    'Generate Token'
                );
                return response()->json($response, 200);
            } else {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Something went wrong'
                ], 500);
            }
    }


    public function validateToken(Request $request)
    {
        $tokenData = TokenModel::where('xutm', $request->token)->first();
        $customer_id = null;
        if(isset($tokenData->decrypted_form_data)){
            $tokenFormData = json_decode($tokenData->decrypted_form_data, true);
            $customer_id = Customer::where('username',credential_encrypt($tokenFormData['customer_id']))->value('id');
        }
    
        if (!$tokenData || $tokenData->deleted_at) {
            return response()->json(['status' => "false", 'data' => [], 'message' => "No Data Found"], 200);
        }
    
        if (now()->diffInMinutes($tokenData->created_at) > 30) {
            return response()->json(['status' => "false", 'data' => [], 'message' => "Token expired"], 200);
        }
    
        $companyList = masterCompany::get();
    
        if ($tokenData->seller_type === "U") {    
            $user = Customer::select('id as seller_id','usertype as usertype_id','name as seller_name','username','email','mobile')->find($tokenData->seller_id);
        } else {
    
            if(config('fetch_sp_details')){
                $user = User::query()
                ->leftJoin('user_additional_data', 'user_additional_data.user_id', '=', 'users.id')
                ->leftJoin('user_branch_relation', 'user_branch_relation.user_id', '=', 'users.id')
                ->leftJoin('au_branch_dump', 'au_branch_dump.branchid', '=', 'user_branch_relation.branch_id')
                ->leftJoin('posp_ic_mappings', 'posp_ic_mappings.user_id', '=', 'users.id')
                ->join('journey_api_token', 'journey_api_token.seller_id', '=', 'users.id')
                ->where('users.id', $tokenData->seller_id)
                ->where('users.status', 'Y')
                ->select([
                    'users.id as seller_id','users.pos_code','users.usertype as usertype_id','users.name as seller_name',
                    'users.username','users.email','users.mobile','users.adhar_no as aadhar_no','users.pan_no',
                    'users.bank_city as city','users.employee_code','users.bank_branch as branch_name',
                    'journey_api_token.seller_type','journey_api_token.created_at','user_additional_data.is_sp',
                    'user_additional_data.sp_name','user_additional_data.sp_code','au_branch_dump.branchcode as branch_code',
                    'posp_ic_mappings.*'])->first();
            }else{
                $user = User::query()
                ->where('users.id', $tokenData->seller_id)
                ->where('users.status', 'Y')
                ->leftJoin('posp_ic_mappings', 'posp_ic_mappings.user_id', '=', 'users.id')
                ->join('journey_api_token', 'journey_api_token.seller_id', '=', 'users.id')
                ->select([
                    'users.id as seller_id','users.pos_code','users.usertype as usertype_id','users.name as seller_name',
                    'users.username','users.email','users.mobile','users.adhar_no as aadhar_no','users.pan_no',
                    'users.bank_city as city','users.employee_code','users.bank_branch as branch_name',
                    'journey_api_token.seller_type','journey_api_token.created_at','posp_ic_mappings.*'])->first();
            }

        }
        
    
        if (!$user) {
            return response()->json(['status' => "false", 'data' => [], 'message' => "No Data Found"], 200);
        }
    
        $decryptUsername = credential_decrypt($user->username);
    
        $user->seller_type  = $tokenData->seller_type;
        $user->usertype     = $tokenData->seller_type;
        $user->seller_name  = $user->seller_name ? credential_decrypt($user->seller_name) : $decryptUsername;
    
        $user->username     = $decryptUsername;
        $user->user_name    = $decryptUsername;
    
        $user->email        = credential_decrypt($user->email);
        $user->mobile       = credential_decrypt($user->mobile);
    
        $user->city = $user->city ? credential_decrypt($user->city) : null;
        $user->branch_name = $user->branch_name ? credential_decrypt($user->branch_name) : null;
        $user->aadhar_no = $user->aadhar_no ? credential_decrypt($user->aadhar_no) : null;
        $user->pan_no = $user->pan_no ? credential_decrypt($user->pan_no) : null;
        $user->unique_number = $user->pos_code ?? null;
    
        $user->first_name = $user->middle_name = $user->last_name = null;
        $user->licence_start_date = $user->licence_end_date = null;
        $user->rm_branch_code = $user->region_name = $user->zone_name = null;
        $user->channel = $user->agent_id = $user->agent_pos_id = null;
        $user->redirection_link = null;
    
        $user->token_created_at = $user->created_at;
        $user->user_id = $customer_id ?? ($user->seller_id ?? null);
    
        $user->branch_code = $user->branch_code ?? null;

        $lob_data = lobMaster::where('id', operator: $tokenData->lob_id)->first();
        $user->lob_name = $lob_data->lob ?? null;

        if(config('ANG.Validation')=="true") {

            $user->business_type = $tokenData->business_type;
            $user->business_code = $tokenData->business_code;
        }
    
        foreach ($companyList as $c) {
            $short = $c->company_shortname;
            if (isset($user->{$short}) && $user->{$short} !== '') {
                $user->{"relation_{$short}"} = $user->{$short};
            }
        }
    
        if($user->seller_type == "P"){
            $userTypeId = getUserTypeIdByIdentifier('Partner');
            
            $checkInMappings = UserMapping::where('user_id', $user->seller_id)->where('user_type', $userTypeId)->first();

            if (empty($checkInMappings)) {

                $roleId = getRoleIdByName('Partner');
                $partnerAdminUserId = User::where('username',credential_encrypt('Partner_admin'))
                ->where('usertype',$userTypeId)->pluck('id')->first();

                UserMapping::insert([
                    'user_id' => $user->seller_id,
                    'user_type' => $userTypeId,
                    'role_id' => $roleId,
                    'reportingto' => $partnerAdminUserId,  
                    'employee_code' => $user->employee_code,
                    'created_at' => Carbon::now(),
                ]);
            }

            $user->h_seller_id = $user->seller_id;
            $user->h_seller_type = 'Partner';
            $user->h_seller_user_name = credential_decrypt($user->username);
            $user->relation_tata_aig = 55554;

        }else{
            $user->h_seller_id = null;
            $user->h_seller_type = null;
            $user->h_seller_user_name = null;
        }
    
        if($user->is_sp=='N'){
            $branch_code = $user->branch_code;
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
                $sp_details_value->user_id = $sp_details_value->users_id;
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
            $user->sp_details = $sp_details;
        }
        $decryptedFormData = $tokenData->decrypted_form_data ?
        json_decode($tokenData->decrypted_form_data, true)
        : [];

        $decryptedFormData['session_id'] = $tokenData->session_id;
        $user->customer_details = $decryptedFormData;

        if(config('showThemeSwitcher')){
            $partner_upper_ids = getUserUpperHierarchy($user->seller_id);
            if(count($partner_upper_ids))
                $ids = array_column($partner_upper_ids, 'id');
            else 
                $ids = [];

            $partner_upper_ids = array_merge($ids, [$user->seller_id]);

            if(count($partner_upper_ids)){
                $sub_partner = PartnerUserMapping::whereIn('user_id',$partner_upper_ids)->first();
                $theme_data_single = ThemeMaster::where('id',$partner->theme_id)->first();
            }
            if($sub_partner){
                $user->sub_partner = 'Y';
                $user->logo         = makeFileUrl($partner->logo);
                $user->favicon_icon = makeFileUrl($partner->favicon_icon);
                $user->theme_value = $theme_data_single->theme_value ?? null;
            }
        }
    
        $tokenData->update(['deleted_at' => now()]);
    
        return response()->json([
            'status' => "true",
            'data' => $user,
            'message' => "Data retrieved successfully"
        ], 200);
    }    

    public function generateUrl(Request $request)
    {
        $user = $request->input('user_id') ? DB::table('users')->where('id', $request->input('user_id'))->first() : Auth::user();

        if (!$user) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'No Data Found'
            ], 500);
        }

        $user_type_name = usertypes::select('name')->where('id', $user->usertype)->first();
        $encodedValue = base_convert(crc32($user_type_name->name), 10, 36);
        $uid = Str::substr($encodedValue . Str::random(10), 0, 10);

        if (empty($user->share_code)) {
            User::where('id', $user->id)->update([
                'share_code' => $uid,
            ]);
            
            return response()->json([
                'status' => 200,
                'return_data' => [
                    'url' => config('Profile.Frontend.Url', '') .'landing-page/' . $uid,
                ],
                'message' => 'Data Inserted successfully'
            ], 200);
        } else {
            return response()->json([
                'status' => 200,
                'return_data' => [
                    'url' => config('Profile.Frontend.Url', '') . 'landing-page/' . $user->share_code,
                ],
                'message' => 'Share code already assigned'
            ], 200);
        } 
    }
    public function getLandingPageData(Request $request)
    {
        $request->validate([
            'share_code' => 'required', 
        ]);

        $share_code = $request->share_code;
       
        $user_details = User::where('share_code', $share_code)->first();
        if (!$user_details) {
            return response()->json([
                'status' => 404,
                'message' => 'No data found for this code'
            ], 404);
        }
        $lobs = DB::table('user_lob_relation as ul')
            ->join('lob_master as l', 'l.id', '=', 'ul.lob_id') 
            ->join('users as u', 'u.id', '=', 'ul.user_id')
            ->where('u.id', $user_details->id)
            ->select('l.*') 
            ->get();

        $lobDataArray = [];
        foreach ($lobs as $lob) {
            $lobDataArray[] = [
                'id' => $lob->id,
                'lob_name' => $lob->lob_name,
                'lob' => $lob->lob,
            ];
        }
           
        try {
            $id = $user_details->id;
            $name = credential_decrypt($user_details->name);
            $email = credential_decrypt($user_details->email);
            $mobile = credential_decrypt($user_details->mobile);
            return response()->json([
                'status' => 200,
                'Data' => [
                    'id' => $id,
                    'name' =>$name,
                    'email' => $email,
                    'mobile' => $mobile,
                ],
                'loblist' => $lobDataArray,
                'message' => 'Data retrieved successfully'
            ], 200);
        } catch (Exception $e) {
            return response()->json([
                'status' => 500,
                'message' => 'Failed to decrypt data'
            ], 500);
        }

        
    }

    public function generateLandingPageToken(Request $request)
    {
        $user = DB::table('users')->where('share_code', $request->input('share_code'))->first();

        if (!$user) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'No Data Found'
            ], 500);
        }
  
        $users = DB::table('users')
            ->when($user->usertype != 0, function ($query) {
                return $query->join('usertypes', 'usertypes.id', '=', 'users.usertype');
            })
            ->where('users.id', $user->id)
            ->first();

        $lobList = lobMaster::select('id', 'lob')->where('is_enabled', 'Y')->get();
        $motorlobarr = ['CAR', 'GCV', 'PCV', 'BIKE', 'MISC'];
        $param = '';
        foreach ($lobList as $key => $value) {
            if (in_array($value->lob, $motorlobarr) && $request->lob_id == $value->id) {
                $param = '?xutm=';
                break;
            } else {
                $param = '?token=';
            }
        }

        $insert = new TokenModel();
        $insert->seller_id = $user->id;
        $insert->seller_type = $user->usertype == 0 ? null : $users->Identifier;
        $insert->xutm = Str::uuid();
        $insert->lob_id = $request->lob_id;
        $insert->save();

        if ($insert) {
            $token = TokenModel::join('lob_master', 'lob_master.id', 'journey_api_token.lob_id')
                ->where('xutm', $insert->xutm)
                ->first();

            return response()->json([
                'status' => 200,
                'return_data' => [
                    $separator = str_contains($token->frontend_url, '?') ? '&' : '?',
                    'frontend_url' => $token->frontend_url . str_replace('?', $separator, $param) . $token->xutm,
                    'redirect_insame_tab' => 0
                ],
                'message' => 'Data Inserted successfully'
            ], 200);
        } else {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Something went wrong'
            ], 500);
        }
    }
    public function generateTokenApi(Request $request)
    {
        $request->validate([
            'username' => 'required|string',
            'password' => 'required|string',
        ]);

        $username = Config('generateTokenApiUsername','Admin');
        $password = Config('generateTokenApiPassword','Admin@123');

        if ($request->username == $username && $request->password == $password) {
            $uuidToken = Str::uuid()->toString();

            $expiryMinutes = Config('generateTokenApiToken_expiry', 30);
            $expiryTime = date("d/m/Y h:i a", strtotime("+$expiryMinutes minutes", time() + 19800));

            SSO::create([
                'sso_api_token' => $uuidToken,
                'status' => 'Y',
            ]);

            return response()->json([
                'status' => 'success',
                'message' => 'Token Generated',
                'token' => $uuidToken,
                'expires_in' => $expiryTime,
            ], 200);
        } else {
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid credentials',
            ], 401);
        }
    }
}
