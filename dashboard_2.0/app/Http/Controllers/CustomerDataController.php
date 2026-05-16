<?php

namespace App\Http\Controllers;

use App\Models\Customer;
use Exception;
use App\Models\User;
use App\Models\lobMaster;
use App\Models\userTypes;
use App\Models\MongoModel;
use Illuminate\Http\Request;
use App\Models\CtaMasterModel;
use App\Models\substagemaster;
use App\Models\StagemasterModel;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Storage;

class CustomerDataController extends Controller
{
    public function customerDashboardData(Request $request)
    {
        $user = Auth::user();
        if (!$user) return response()->json(['message' => 'Unauthorized'], 401);

        $user_id = (string) $user->id;
        $today = now();
        $oneMonthLater = now()->addMonth();
        
        $stage = StagemasterModel::select('id', 'sub_stage_name')->where('stage_name', 'Issued')->first();
        if (!$stage) return response()->json(['message' => 'Stage not found'], 404);
        
        $subStageList = explode(',', $stage->sub_stage_name);
        $subStagesArr = substagemaster::whereIn('id', $subStageList)->pluck('sub_stage_name')->toArray();

        $baseQuery = MongoModel::where('user_id', $user_id)->select(
            'trace_id', 'proposer_name', 'proposer_mobile', 'proposer_emailid',
            'vehicle_registration_number', 'company_name', 'transaction_stage',
            'proposal_no', 'policy_no', 'proposal_url', 'quote_url', 'section',
            'policy_start_date', 'policy_end_date', 'lastupdated_time', 'policy_doc_path'
        );

        // Query for getCustomerData
        $customerDataQuery = (clone $baseQuery)->whereIn('transaction_stage', $subStagesArr);
        $customerDataQuery = (clone $baseQuery)->whereIn('seller_type', ["U","b2c"]);
        $nearExpiryPolicies = (clone $customerDataQuery)->whereBetween('policy_end_date', [$today, $oneMonthLater])->count();
        $customerData = (clone $customerDataQuery)->when($nearExpiryPolicies, fn($q) => $q->whereBetween('policy_end_date', [$today, $oneMonthLater]))->limit(3)->get();

        $customerData = $customerData->filter(fn($policy) => \Carbon\Carbon::parse($policy->policy_end_date)->startOfDay()->greaterThan($today->copy()->startOfDay()))
        ->map(fn($policy) => tap($policy, function ($p) use ($today) {
            $p->days_left = $today->copy()->startOfDay()->diffInDays(\Carbon\Carbon::parse($p->policy_end_date)->startOfDay());
            if (!empty($p->policy_doc_path) && config('s3_download_link') == true) {
                $parsedUrl = parse_url($p->policy_doc_path);
                if (!empty($parsedUrl['path'])) {
                    $fileKey = ltrim($parsedUrl['path'], '/');
                    $p->policy_doc_path = Storage::disk('s3')->temporaryUrl(
                        $fileKey,
                        now()->addDays(7)
                    );
                }
            }
            return $p;
        }))->values();

        // Query for getCustomerRecentData
        $customerRecentDataQuery = (clone $baseQuery)->whereNotIn('transaction_stage', $subStagesArr)->whereIn('seller_type', ["U","b2c"])->orderBy('lastupdated_time', 'desc');
        if ($request->section) $customerRecentDataQuery->where('section', $request->section);
        
        $subStageMap = substagemaster::pluck('id', 'sub_stage_name'); 
        $stageMap = StagemasterModel::select('id', 'sub_stage_name')->get()->mapWithKeys(function ($stage) {
            return [$stage->id => explode(',', $stage->sub_stage_name)];
        });
        $ctaMap = CtaMasterModel::pluck('cta_name', 'stage'); 

        $customerRecentData = $customerRecentDataQuery->get()->map(function ($item) use ($subStageMap, $stageMap, $ctaMap) {
            $subStageId = $subStageMap[$item->transaction_stage] ?? null;
            if (!$subStageId) {
                $item['common_redirect_url'] = null;
                return $item;
            }

            $stageId = collect($stageMap)->search(fn($subStages) => in_array($subStageId, $subStages));
            if (!$stageId) {
                $item['common_redirect_url'] = null;
                return $item;
            }

            $ctaData = $ctaMap[$stageId] ?? null;
            $item['common_redirect_url'] = $ctaData && isset($item[$ctaData]) ? $item[$ctaData] : $ctaData;
            
            return $item;
        });

        return response()->json([
            'message' => 'Success',
            'mypoliciesData' => $customerData,
            'recentSummaryData' => $customerRecentData,
        ], 200);
    }

    public function getCustomerData()
    {
        $user = Auth::user();
        $user_id = strval($user->id);

    
        $stage = StagemasterModel::select('id', 'sub_stage_name')->where('stage_name', 'Issued')->first();
        if (!$stage) {
            return response()->json(['message' => 'Stage not found'], 404);
        }

        $subStageList = explode(',', $stage->sub_stage_name);
        $SubStages = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();
        $query = MongoModel::select(
            'trace_id', 'proposer_name', 'proposer_mobile', 'proposer_emailid',
            'vehicle_registration_number', 'company_name', 'transaction_stage',
            'proposal_no', 'policy_no', 'proposal_url', 'section',
            'policy_start_date', 'policy_end_date', 'user_id', 'lastupdated_time'
        )->whereIn('transaction_stage', $subStagesArr)
        ->whereIn('seller_type', ["U","b2c"])
        ->where('user_id', $user_id);

        $today = now(); 
        $oneMonthLater = now()->addMonth(); 

        $nearExpiryPolicies = (clone $query)->whereBetween('policy_end_date', [$today, $oneMonthLater])->count();

        if ($nearExpiryPolicies > 0) {
            $data = (clone $query)->whereBetween('policy_end_date', [$today, $oneMonthLater])->limit(3)->get();
        } else {
            $data = $query->limit(3)->get();
        }

        $data = $data->filter(function ($policy) use ($today) {
            $expiryDate = \Carbon\Carbon::parse($policy->policy_end_date)->startOfDay();
            $todayDate = $today->copy()->startOfDay();
            return $expiryDate->greaterThan($todayDate);
        })->map(function ($policy) use ($today) {
            $expiryDate = \Carbon\Carbon::parse($policy->policy_end_date)->startOfDay();
            $todayDate = $today->copy()->startOfDay();
            $policy->days_left = $todayDate->diffInDays($expiryDate);
        
            return $policy;
        })->values(); 

        if ($data->isNotEmpty()) {
            return response()->json($data);
        } else {
            return response()->json(['message' => 'Data not found'], 404);
        }
    }

    public static function getCustomerRecentData(Request $request)
    {
        $user_details = Auth::user();
        if (!$user_details) {
            return response()->json(['message' => 'Unauthorized'], 401);
        }
    
        $section = $request->section;
        $userTypeData = userTypes::select('id', 'name', 'Identifier')
            ->where('id', optional($user_details)->usertype)
            ->first();
        $userid = strval($user_details->id);    
        $stage = StagemasterModel::select('id', 'sub_stage_name', 'stage_name')
            ->where('stage_name', 'Issued')
            ->first();
    
        if (!$stage) {
            return response()->json(['message' => 'Stage not found'], 404);
        }
    
        $subStageList = explode(',', $stage->sub_stage_name);
        $SubStages = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();
    
        $query = mongomodel::select(
            'trace_id', 'proposer_name', 'proposer_mobile', 'proposer_emailid', 
            'vehicle_registration_number', 'company_name', 'transaction_stage', 
            'proposal_no', 'policy_no', 'proposal_url', 'quote_url', 'section', 
            'policy_start_date', 'policy_end_date', 'lastupdated_time'
        )->where('user_id', $userid)
        ->whereIn('seller_type', ["U","b2c"])
        ->whereNotIn('transaction_stage', $subStagesArr)
        ->orderBy('lastupdated_time', 'desc');
    
        if (!empty($section)) {
            $query->where('section', $section);
        }
    
        $data = $query->get();
    
        if ($data->isEmpty()) {
            return response()->json(['message' => 'Data not found'], 404);
        }
    
        $data = $data->map(function ($item) {
            $lob = $item->section; 
            $transactionStage = $item->transaction_stage; 
    
       
            $substageName = substagemaster::select('id', 'sub_stage_name')
                ->where('sub_stage_name', $transactionStage)
                ->first();
    
            if (!$substageName) {
                $item['common_redirect_url'] = null;
                return $item;
            }
    
            $subStageId = $substageName->id;
    
            $stagename = StagemasterModel::select('stage_name')
                ->whereRaw("FIND_IN_SET(?, sub_stage_name)", [$subStageId])
                ->first();
    
            if (!$stagename) {
                $item['common_redirect_url'] = null;
                return $item; 
            }
    
            $ctaData = CtaMasterModel::select('cta_name')
                ->where('stage_name', $stagename->stage_name)
                ->where('lob_name', $lob)
                ->first();
    
            $item['common_redirect_url'] = $ctaData ? $ctaData->cta_name : null;
            if ($item['common_redirect_url'] == 'proposal_url') {
                $item['common_redirect_url'] = $item['proposal_url'];
            } elseif ($item['common_redirect_url'] == 'quote_url') {
                $item['common_redirect_url'] = $item['quote_url']; 
            }
            
            return $item;
        });
    
        return response()->json($data);
    }

    public function getPolicyDetails()
    {
        $user =Auth::user();
        $user_id = strval($user->id);
        $section = request('section');
        // $seller_type = request('seller_type');
    
        if (empty($user_id)) {
            return response()->json([
                'message' => 'User ID is required',
            ], 400);
        }
        $stage= StagemasterModel::select('id','sub_stage_name')->where('stage_name','Issued')->first();
        $subStageList = $stage->sub_stage_name;
        $subStageList = explode(',', $subStageList);
        $SubStages  = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();
    
        $query = MongoModel::select(
            'trace_id', 'proposer_name', 'proposer_mobile', 'proposer_emailid',
            'vehicle_registration_number', 'company_name', 'transaction_stage',
            'proposal_no', 'policy_no', 'proposal_url', 'section',
            'policy_start_date', 'policy_end_date', 'user_id', 'lastupdated_time', 'seller_id', 'seller_type','policy_doc_path'
        )->whereIn('transaction_stage', $subStagesArr)->whereIn('seller_type', ["U","b2c"])->where('user_id', $user_id);
    
        if (!empty($section)) {
            $query->where('section', $section);
        }
        // if (!empty($seller_type)) {
        //     $query->where('seller_type', $seller_type);
        // }
    
        $data = $query->get();
    
        if ($data->isEmpty()) {
            return response()->json([
                'message' => 'Data not found',
            ], 404);
        }
        foreach ($data as $value) {
            if (!empty($value->policy_doc_path) && config('s3_download_link') == true) {
                $parsedUrl = parse_url($value->policy_doc_path);
                
                if (!empty($parsedUrl['path'])) {
                    $fileKey = ltrim($parsedUrl['path'], '/'); 
            
                    $value->policy_doc_path = Storage::disk('s3')->temporaryUrl(
                        $fileKey,
                        now()->addDays(7)
                    );
                }
            }
        }
    
        return response()->json([
            'message' => 'Success',
            'data' => $data,
        ], 200);
    }

    public function upcomingRenewals()
    {
        $section = request('section');
        $dateRange = request('date_range', 1);
    
        $today = now(); 
        $renewalDate = now()->addMonths($dateRange);
    
        $query = MongoModel::select(
            'trace_id', 'proposer_name', 'proposer_mobile', 'proposer_emailid',
            'vehicle_registration_number', 'company_name', 'transaction_stage',
            'proposal_no', 'policy_no', 'proposal_url', 'section',
            'policy_start_date', 'policy_end_date', 'user_id', 'lastupdated_time', 
            'seller_id', 'seller_type'
        );
    
        if (!empty($section)) {
            $query->where('section', $section);
        }
    
        $query->whereBetween('policy_end_date', [$today, $renewalDate])->whereIn('seller_type', ["U","b2c"]);
    
        $data = $query->limit(10)->get();
    
        if ($data->isEmpty()) {
            return response()->json([
                'message' => 'Data not found',
            ], 404);
        }
    
        return response()->json([
            'message' => 'Success',
            'data' => $data,
        ], 200);
    }

    public function getCustomerList(){
        $usertypeId = getUserTypeIdByIdentifier('U');

        $formatedCustomerData = [];
         $customerUser = User::select('id','name','username','mobile')->where('usertype',$usertypeId)->get();

         foreach($customerUser as $c => $v){
            $formatedCustomerData[] =[
                'id' => $v->id,
                'name' => credential_decrypt($v->name),
                'username' => credential_decrypt($v->username),
                'mobile' => credential_decrypt($v->mobile),
            
            ];
         }


         return $formatedCustomerData;
    }
    public function editCustomerProfile(Request $request)
    {
        try {
            $user = Auth::user();
 
            if (!$user) {
                return response()->json(['status' => 401, 'message' => 'Unauthorized'], 401);
            }
             $model = $user->usertype != "5" ? User::class : Customer::class;
    
            if (!empty($request)) {
                $data = $model::where('id', $user->id)->update([
                    'name' => credential_encrypt($request->name),
                    'email' => credential_encrypt($request->email),
                    'username' => credential_encrypt($request->username),
                    'mobile' => credential_encrypt($request->mobile),
                    'account_holder_name' => credential_encrypt($request->accountHolderName),
                    'account_no' => credential_encrypt($request->accNumber),
                    'ifsc_code' => credential_encrypt($request->ifsc),
                    'bank_name' => credential_encrypt($request->bankName),
                    'bank_city' => credential_encrypt($request->bankCity),
                    'bank_branch' => credential_encrypt($request->bankBranch ?? null), 
                ]);

                if ($data) {
                    return ([
                        "status" => 200,
                        "message" => "Data Updated Successfully"
                    ]);
                } else {
                    return ([
                        'status' => 404,
                        'message' => 'Data Not Found'
                    ]);
                }
            } else {
                return ([
                    'status' => 500,
                    'message' => 'Data Not Found'
                ]);
            }
    
        } catch (Exception $e) {
            return response()->json(['status' => 500, 'message' => 'Something went wrong', 'error' => $e->getMessage()], 500);
        }
    }

    public function viewCustomerPolicy(Request $request)
    {
        $trace_id = $request->trace_id;
        $user = Auth::user();
        $user_id = strval($user->id);

        if (empty($user_id)) {
            return response()->json(['message' => 'User ID is required'], 400);
        }

        $stage = StagemasterModel::select('id', 'sub_stage_name')->where('stage_name', 'Issued')->first();

        if (!$stage || empty($stage->sub_stage_name)) {
            return response()->json(['message' => 'No issued stage found'], 404);
        }

        $subStageList = explode(',', $stage->sub_stage_name);
        $SubStages = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();

        if (empty($trace_id)) {
            return response()->json(['message' => 'Trace ID is required'], 400);
        }

        $policy = MongoModel::where('user_id', $user_id)
            ->where('trace_id', $trace_id)
            ->whereIn('seller_type', ["U","b2c"])
            ->whereIn('transaction_stage', $subStagesArr)
            ->select('policy_doc_path')
            ->first();

        if (!$policy || empty($policy->policy_doc_path)) {
            return response()->json(['message' => 'Policy document not found'], 404);
        }

        return response()->download(storage_path('app/public/' . $policy->policy_doc_path), 'policy_document.pdf', [
            'Content-Type' => 'application/pdf',
        ]);
    }

    public function customerLobs()
    {
        $loblist = lobMaster::select('id', 'lob_name', 'lob')
            ->where('is_enabled', 'Y')
            ->get(); 

        if ($loblist->isEmpty()) { 
            return response()->json([
                'message' => 'loblist not found',
            ], 404);
        }

        return response()->json([
            'message' => 'Success',
            'lobs' => $loblist->toArray(), 
        ], 200);
    }
    
}
