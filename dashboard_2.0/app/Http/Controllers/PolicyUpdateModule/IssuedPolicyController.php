<?php

namespace App\Http\Controllers\PolicyUpdateModule;

use App\Exports\IssuedPolicyExport;
use App\Exports\policyDetailsCancelLogsExport;
use App\Exports\policyDetailsUpdateLogsExport;
use App\Http\Controllers\Controller;
use App\Models\CancelLogsCollectionModel;
use App\Models\MongoModel;
use App\Models\UpdateLogsCollectionModel;
use App\Models\UpdateStageLogDashboardAction;
use App\Services\ThirdPartyTokenService;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Carbon\Carbon;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Auth;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Str;
use Maatwebsite\Excel\Facades\Excel;
use MongoDB\Laravel\Eloquent\Casts\ObjectId as CastsObjectId;
class IssuedPolicyController extends Controller
{
    protected $tokenService;

    protected $auth;

    public function __construct(ThirdPartyTokenService $tokenService)
    {
        $this->tokenService = $tokenService;
        $this->auth = Auth::user();

    }
    public function issuedPolicesList(Request $request)
    {
        $listingPermission = ["policy-details.view","Policy Details.view"];
        if (!$this->auth->hasAnyPermission($listingPermission)) {
            return response()->json([
                'status' => 403,
                'message' => "You don't have permission to view this page"
            ], 403);
        }

        $column_head = [
            ["header" => "Trace ID", "accessorKey" => "trace_id", "isActions" => false],
            ["header" => "Policy Number", "accessorKey" => "policy_no", "isActions" => false],
            ["header" => "Proposer Name", "accessorKey" => "proposer_name", "isActions" => false],
            ["header" => "Proposer Mobile", "accessorKey" => "proposer_mobile", "isActions" => false],
            ["header" => "Proposer Email ID", "accessorKey" => "proposer_emailid", "isActions" => false],
            ["header" => "Section", "accessorKey" => "section", "isActions" => false],
            ["header" => "Seller Type", "accessorKey" => "seller_type", "isActions" => false],
            ["header" => "Policy Type", "accessorKey" => "is_offline_entry", "isActions" => false],
            ["header" => "Created On", "accessorKey" => "created_at", "isActions" => false],

        ];

        $perPage = $request->input('size', 10);
        $policyType = $request->input('policy_type'); 
        $lob = $request->input('section');
        $search = $request->input('search', '');

        $policy_result = MongoModel::select('_id','trace_id', 'policy_no', 'proposer_name', 'proposer_mobile', 'proposer_emailid', 'section', 'seller_type', 'is_offline_entry','created_at')
            ->whereIn('transaction_stage', ['Policy Issued', 'Policy Issued pdf generated', 'Policy Issued, but pdf not generated'])
            ->orderBy('created_at', 'desc');

        $start_date = $request->input('start_date'); 
        $end_date = $request->input('end_date');   

        if ($start_date && $end_date) {
            $startDate = Carbon::parse($request->start_date)->startOfDay();
            $endDate = Carbon::parse($request->end_date)->endOfDay();
            $policy_result->whereBetween('created_at', [$startDate, $endDate]);

        }

        if (!is_null($policyType)) {
            $policy_result->where('is_offline_entry',  $policyType); // expecting 0 or 1
        }

        if (!empty($lob)) {
            $policy_result->where('section', $lob);
        }
        if(Auth::user()->usertype == 4){
            $utmParameter = activeRoleCodeMappingUser();
            if (!empty($utmParameter)) {
                $policy_result = $policy_result->where(function ($query) use ($utmParameter) {
                    foreach ($utmParameter as $key => $value) {
                        $query->where('broker_'.$key, $value);
                    }
                });
            }   
        }
        
        if ($request->has('search') && !empty($search)) {
            $policy_result->where(function ($query) use ($search) {
                $query->where('trace_id', 'regex', '/' . $search . '/i')
                    ->orWhere('policy_no', 'regex', '/' . $search . '/i')
                    ->orWhere('proposer_name', 'regex', '/' . $search . '/i')
                    ->orWhere('proposer_mobile', 'regex', '/' . $search . '/i')
                    ->orWhere('proposer_emailid', 'regex', '/' . $search . '/i')
                    ->orWhere('section', 'regex', '/' . $search . '/i')
                    ->orWhere('seller_type', 'regex', '/' . $search . '/i');
            });
        }
        if ($request->has('export') && $request->input('export') == true) {
            $policy_results = $policy_result->get();
        }else{
            $policy_results = $policy_result->paginate($perPage);
        }

        $dataFormatting = $policy_results->values();

        $transformedData = $dataFormatting->map(function ($item) {
            return [
                'id' => $item->_id,
                'trace_id' =>  "'".$item->trace_id,
                'policy_no' => $item->policy_no,
                'proposer_name' => $item->proposer_name,
                'proposer_mobile' => $item->proposer_mobile,
                'proposer_emailid' => $item->proposer_emailid,
                'section' => $item->section,
                'seller_type' => $item->seller_type,
                'is_offline_entry' => $item->is_offline_entry == 1 ? 'Offline' : 'Online',
                'created_at' => $item->created_at ? $item->created_at->toDateTime()->format('d/m/Y H:i:s') : null,
            ];
        });

        if($request->has('export') && $request->input('export') == true){

            $fileName = 'issuedPolicy_data_' . now()->timestamp . '.xlsx';
            $filePath = 'exports/' . $fileName;

            Excel::store(new IssuedPolicyExport($transformedData), $filePath, 'public');
            $downloadLink = asset(Storage::url($filePath));

            return response()->json([
                'status' => 200,
                'message' => "Excel file generated successfully",
                'data' => $downloadLink
            ]);
        }

        if (!empty($transformedData)) {
            return response()->json([
                'status' => 200,
                'column_head' => $column_head,
                'return_data' => $transformedData,
                'pagination' => [
                    'total_records' => $policy_results->total(),
                    'total_pages' => $policy_results->lastPage(),
                    'current_page' => $policy_results->currentPage(),
                    'per_page' => $policy_results->perPage(),
                ],
            ]);
        } else {
            return response()->json([
                'status' => 500,
                'message' => "No Data Found",
                'return_data'=>[]
            ]);
        }
    }

    public function editPolicy(Request $request)
    {
        $editPermission = ["policy-details.edit","Policy Details.edit"];
        if (!$this->auth->hasAnyPermission($editPermission)) {
            return response()->json([
                'status' => 403,
                'message' => "You don't have permission to edit"
            ], 403);
        }

        $record = MongoModel::find($request->id);

        if (!$record) {
            return response()->json(['message' => 'Record not found'], 404);
        }

        if(!empty($record->company_name)){
            $ic_id = DB::table('ic_master')
            ->where('ic_name', $record->company_name)
            ->value('ic_id') ?? null;
        }else{
            $ic_id =  null;
        }
        
        if(!empty($record->policy_type)){
            $policy_type_id = DB::table('policy_type_master')
            ->where('policy_type_name', $record->policy_type)
            ->value('type_id') ?? null;
        }else{
            $policy_type_id =  null;
        }
        

        if (!empty($record->policy_category_name)) {
            $policy_category_id = DB::table('policy_category')->where('category_name', $record->policy_category_name)
                ->value('category_id') ?? null;
        }else{
            $policy_category_id = null;
        }
        

        $formatted = [
            'section'               => $record->section,
            'policy_number'         => $record->policy_no ?? null, 
            'trace_id'              => $record->trace_id,
            'screenshotFile'        => null, 
            'screenshot_content'    => null, 
            'ss_type'               => null, 
            'user_id'               => $record->user_id, // jisne login kiya //IT IS IN MONGO
            'is_offline_entry'      => $record->is_offline_entry,
            'seller_id'             => $record->seller_id,
            'seller_name'           => $record->seller_name,
            'seller_username'       => $record->seller_username,
            'seller_mobile'         => $record->seller_mobile,
            'seller_email'          => $record->seller_email,
            'seller_type'           => $record->seller_type ?? null, //dropdown hay E,P pOS
            'seller_business_type'  => $record->seller_business_type,
            'seller_business_code'  => $record->seller_business_code,
            'policy_start_date'     => $record->policy_start_date ?? null,
            'policy_end_date'       => $record->policy_end_date ?? null,
            'customer_name'             => $record->proposer_name, 
            'email'                     => $record->proposer_emailid ?? null,
            'proposer_mobile'           => $record->proposer_mobile ?? null,
            'ic_name_id'                => $ic_id ?? null, // company_name in mongo
            'ic_name'                   => $record->company_name ?? null,
            'policy_type'               => $record->policy_type ?? null, 
            'policy_type_id'           =>  $policy_type_id ?? null, 
            'policy_tenture_days'       => $record->policy_tenture_days,
            'bank_branch_name'          => null, // Not present // branch_name in mongobd
            'policy_period'             => $record->policy_period,
            'policy_category_id'        => $policy_category_id ?? null,  //policy_category_name mongo mai hay {getting from query}
            'policy_category_name'      => $record->policy_category_name ?? null, // KEY IN MONGO
            'vehicle_make'              => $record->vehicle_make,
            'vehicle_model'             => $record->vehicle_model,
            'vehicle_version'           => $record->vehicle_version,
            'vehicle_registration_number' => $record->vehicle_registration_number,
            'vehicle_age'               => $record->vehicle_age,
            'vehicle_manufacture_year'  => $record->vehicle_manufacture_year,

        ];
        
        return response()->json([
            'status' => 200,
            'message' => "Policy Details",
            'data' => [
              'prefilData' => $formatted,
              'isOffline' => $record->is_offline_entry == 1 ? 'Offline' : 'Online',
            ]
        ]);

    }

    public function updateIssuedPolices(Request $request)
    {
        $editPermission = ["policy-details.edit","Policy Details.edit"];
        if (!$this->auth->hasAnyPermission($editPermission)) {
            return response()->json([
                'status' => 403,
                'message' => "You don't have permission to edit"
            ], 403);
        }
       
        $auth = Auth::user();

        $requestedSection = strtoupper($request->section);

        $motorLob = ['CAR','BIKE','MISC','GCV','PCV','MOTOR'];
        $healthLob = ['HEALTH','TOP_UP'];

        if(in_array($requestedSection,$motorLob)){
            $requestedSection = 'MOTOR';
        }
        if(in_array($requestedSection,$healthLob)){
            $requestedSection = 'HEALTH';
        }

        if (trim($requestedSection) == 'HEALTH') {
            $apiUrl = config('Policy.Update.Health');
        } else if(trim($requestedSection) == 'MOTOR'){
            $apiUrl =config('Policy.Update.Motor');
        }

        $token = $this->tokenService->getToken($apiUrl);
 
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Validation' => $token,
        ];

        $methodType = 'POST';
        $body = [
            "section" => strtolower($requestedSection),
            "policy_number" => $request->policy_number,
            "trace_id" => $request->trace_id,
            "screenshotFile" => $request->screenshotFile,
            "screenshot_content" => $request->screenshot_content,
            "ss_type" => $request->ss_type,
            "user_id" => $auth->id,
            "is_offline_entry" => $request->is_offline_entry,

            "seller_id" => $request->seller_id,
            "seller_name" => $request->seller_name, //10
            "seller_username" => $request->seller_username,
            "seller_mobile" => $request->seller_mobile,
            "seller_email" => $request->seller_email,
            "seller_type" => $request->seller_type,
            "seller_business_type" => $request->seller_business_type,
            "seller_business_code" => $request->seller_business_code, //16

            "data" => [
                "customer_name" => $request['customer_name'] ?? null,
                "email" => $request['email'] ?? null,
                "mobile" => $request['mobile'] ?? null,
                "trace_id" => $request['trace_id'] ?? null,
                "ic_name_id" => $request['ic_name'] ?? null,  
                "policy_type" => $request['policy_type'] ?? null, 
                "policy_tenture_days" => $request['policy_tenture_days'] ?? null,
                "bank_branch_name" => $request['bank_branch_name'] ?? null,
                "policy_period" => $request['policy_period'] ?? null,
                "policy_category_id" => $request['policy_category'] ?? null,
                "vehicle_make" => $request['vehicle_make'] ?? null,
                "vehicle_model" => $request['vehicle_model'] ?? null,
                "vehicle_version" => $request['vehicle_version'] ?? null,
                "vehicle_registration_number" => $request['vehicle_registration_number'] ?? null,
                "vehicle_age" => $request['vehicle_age'] ?? null,
                "vehicle_manufacture_year" => $request['vehicle_manufacture_year'] ?? null,
            ]
        ];

        try {

            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'Policy-Update'
                );
            }

            return $data;
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'Policy-Update'

                );
            }
            return response()->json([
                'status' => 500,
                'message' => "Something went wrong",
                'error' => $e->getMessage()
            ]);
        }
    }

    public function cancelIssuedPolicy(Request $request)
    {
        $deletePermission = ["policy-details.delete","Policy Details.delete"];
        if (!$this->auth->hasAnyPermission($deletePermission)) {
            return response()->json([
                'status' => 403,
                'message' => "You don't have permission to delete"
            ], 403);
        }
        $auth = Auth::user();
      
        $requestedSection = strtoupper($request->section);

        $motorLob = ['CAR','BIKE','MISC','GCV','PCV','MOTOR'];
        $healthLob = ['HEALTH','TOP_UP'];

        if(in_array($requestedSection,$motorLob)){
            $requestedSection = 'MOTOR';
        }
        if(in_array($requestedSection,$healthLob)){
            $requestedSection = 'HEALTH';
        }


        if (trim($requestedSection) == 'HEALTH') {
            $apiUrl = config('Policy.Cancel.Health');
        } else if(trim($requestedSection) == 'MOTOR'){
            $apiUrl = config('Policy.Cancel.Motor');
        }

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Validation' => $token,
        ];

        $methodType = 'POST';
        $body = [
            "section" => strtolower($requestedSection),
            "policy_number" => $request->policy_number,
            "trace_id" => $request->trace_id,
            "screenshotFile" => $request->screenshotFile,
            "screenshot_content" => $request->screenshot_content,
            "ss_type" => $request->ss_type,
            "user_id" => $auth->id,
            "is_offline_entry" => $request->is_offline_entry
        ];

        try {

            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'Policy-Update'
                );
            }

            return response()->json([
                // 'status' => 200,
                // 'message' => "Policy Cancelled Successfully",
                'data' => $data
            ]);
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'Policy-Update'

                );
            }
            return response()->json([
                'status' => 500,
                'message' => "Something went wrong",
                'error' => $e->getMessage()
            ]);
        }
    }

    public function policyDetailsUpdateLogs(Request $request){
        
        $listingPermission = ["policy update Logs.view","Policy Update logs.view"];
        if (!$this->auth->hasAnyPermission($listingPermission)) {
            return response()->json([
                'status' => 403,
                'message' => "You don't have permission to view this page"
            ], 403);
        }


        $column_head = [
            ["header" => "Sr No.", "accessorKey" => "sr_no", "isActions" => false],
            ["header" => "Trace ID", "accessorKey" => "trace_id", "isActions" => false],
            ["header" => "Policy Number", "accessorKey" => "policy_no", "isActions" => false],
            ["header" => "Section", "accessorKey" => "section", "isActions" => false],
            ["header" => "Policy Type", "accessorKey" => "is_offline_entry", "isActions" => false],
            ["header" => "Action Type", "accessorKey" => "action_type", "isActions" => false],
            ["header" => "Updated Timestamp", "accessorKey" => "update_timestamp", "isActions" => false],
            ["header" => "Screenshot", "accessorKey" => "screenshot", "isActions" => false],
        ];
        $page = $request->input('page',1);
        $perPage = $request->input('size', 10);

        $search = $request->search;
        
        if($request->has('export') && $request->export == true){
            $data=UpdateLogsCollectionModel::orderBy('created_at', 'desc')->get();
        }else{
            $data=UpdateLogsCollectionModel::orderBy('created_at', 'desc')->paginate($perPage);
        }
        
        $transformedData = $data->map(function ($item,$index) use($page,$perPage) {
            return [
                'sr_no'   => $page * $perPage - $perPage + ($index + 1),
                'trace_id' => $item->trace_id ?? null,
                'policy_no' => $item->policy_number ?? null,
                'section' => $item->section ?? null,
                'is_offline_entry' => isset($item->is_offline_entry) ? ($item->is_offline_entry == 1 ? 'Offline' : 'Online') : null,
                'action_type' => $item->action_type ?? null,
                'update_timestamp' => !empty($item->updated_at)
                ? Carbon::parse($item->updated_at)->format('d/m/Y H:i:s')
                : null,
                'screenshot' => $item->screenshot ?? null,
                'old_data' => json_encode($item['old_data'] ?? $item['old_record'] ?? null),
                'new_data' => json_encode($item['new_data'] ?? $item['new_record'] ?? null),

            ];
        });

        if($request->has('export') && $request->export == true){
            $fileName = 'policy_details_update_logs' . now()->format('Y_m_d_H_i_s') . '.xlsx';

            Excel::store(new policyDetailsUpdateLogsExport($transformedData), $fileName, 'public');
        
            $downloadUrl = Storage::disk('public')->url($fileName);
        
            return response()->json([
                'status' => true,
                'message' => 'Export successful',
                'download_url' => $downloadUrl
            ]);
        }


        if ($request->has('search') && !empty($search)) {
            $filtered = $transformedData->filter(function ($item) use ($search) {
                return Str::contains(strtolower($item['trace_id']), strtolower($search)) ||
                       Str::contains(strtolower($item['policy_no']), strtolower($search)) ||
                       Str::contains(strtolower($item['section']), strtolower($search)) ||
                       Str::contains(strtolower($item['is_offline_entry']), strtolower($search)) ||
                       Str::contains(strtolower($item['action_type']), strtolower($search));
            });
        
            $transformedData = $filtered->values(); 
        }

        if (!empty($transformedData)) {
            return response()->json([
                'status' => 200,
                'column_head' => $column_head,
                'return_data' => $transformedData,
                'pagination' => [
                    'current_records_count' => $transformedData->count(),
                    'total_records' => $data->total(),
                    'total_pages' => $data->lastPage(),
                    'current_page' => $data->currentPage(),
                    'per_page' => $data->perPage(),
                ],
            ]);
        }else{
            return response()->json([
                'status' => 500,
                'message' => 'No Data Found',
                'return_data' => []
                
            ]);
        }

    }

    public function policyDetailsCancelLogs(Request $request){
        
        $listingPermission = ["policy cancel Logs.view","Policy Cancel logs.view"];
        if (!$this->auth->hasAnyPermission($listingPermission)) {
            return response()->json([
                'status' => 403,
                'message' => "You don't have permission to view this page"
            ], 403);
        }

        $column_head = [
            ["header" => "Sr No.", "accessorKey" => "sr_no", "isActions" => false],
            ["header" => "Trace ID", "accessorKey" => "trace_id", "isActions" => false],
            ["header" => "Policy Number", "accessorKey" => "policy_no", "isActions" => false],
            ["header" => "Section", "accessorKey" => "section", "isActions" => false],
            ["header" => "Policy Type", "accessorKey" => "is_offline_entry", "isActions" => false],
            ["header" => "Action Type", "accessorKey" => "action_type", "isActions" => false],
            ["header" => "Updated Timestamp", "accessorKey" => "update_timestamp", "isActions" => false],
            ["header" => "Screenshot", "accessorKey" => "screenshot", "isActions" => false],
        ];

        $page = $request->input('page',1);
        $perPage = $request->input('size', 10);

        $search = $request->search;
        
        if($request->has('export') && $request->export == true){
           $data = CancelLogsCollectionModel::all()->sortByDesc('created_at')->toArray();

        }else{
            $forPaginationResult= CancelLogsCollectionModel::orderBy('created_at', 'desc')->paginate($perPage);
             $paginatedData= $forPaginationResult->toArray();
             $data = $paginatedData['data'];
        }

  
        $data = array_map(function($item) {
            return (array) $item;
        }, $data);

        // Reindex array from 0
        $data = array_values($data);

        $transformedData = array_map(function ($item, $index) use ($page, $perPage) {

            return [
                'sr_no'   => (int)$page * (int)$perPage - (int)$perPage + ($index + 1),
                'trace_id' => $item['trace_id'] ?? null,
                'policy_no' => $item['policy_number'] ?? null,
                'section' => $item['section'] ?? null,
                'is_offline_entry' => isset($item['is_offline_entry']) ? ($item['is_offline_entry'] == 1 ? 'Offline' : 'Online') : null,
                'action_type' => $item['action_type'] ?? null,
                'update_timestamp' => !empty($item['updated_at'])
                    ? Carbon::parse($item['updated_at'])->format('d/m/Y H:i:s')
                    : null,
                'screenshot' => $item['screenshot'] ?? null,
                'old_data' => json_encode($item['old_data'] ?? $item['old_record'] ?? null),
                'new_data' => json_encode($item['new_data'] ?? $item['new_record'] ?? null),
            ];
        }, $data, array_keys($data));


        if($request->has('export') && $request->export == true){

            $fileName = 'policy_details_cancel_logs' . now()->format('Y_m_d_H_i_s') . '.xlsx';

            Excel::store(new policyDetailsCancelLogsExport($transformedData), $fileName, 'public');
        
            $downloadUrl = Storage::disk('public')->url($fileName);
        
            return response()->json([
                'status' => true,
                'message' => 'Export successful',
                'download_url' => $downloadUrl
            ]);
        }

        if ($request->has('search') && !empty($search)) {
            $searchTerm = strtolower($search); // make search case-insensitive
            $transformedData = collect($transformedData)->filter(function ($item) use ($searchTerm) {
                return Str::contains(strtolower($item['trace_id']), $searchTerm) ||
                       Str::contains(strtolower($item['policy_no']), $searchTerm) ||
                       Str::contains(strtolower($item['section']), $searchTerm) ||
                       Str::contains(strtolower($item['is_offline_entry'] ?? ''), $searchTerm) ||
                       Str::contains(strtolower($item['action_type']), $searchTerm);
            })->values()->toArray(); 
        }

        if (!empty($transformedData)) {
            return response()->json([
                'status' => 200,
                'column_head' => $column_head,
                'return_data' => $transformedData,
                'pagination' => [
                    'total_records' => $forPaginationResult->total(),
                    'total_pages' => $forPaginationResult->lastPage(),
                    'current_page' => $forPaginationResult->currentPage(),
                    'per_page' => $forPaginationResult->perPage(),
                ],
            ]);
        }else{
            return response()->json([
                'status' => 500,
                'message' => 'No Data Found',
                'return_data' => []
                
            ]);
        }
    }

    public function getIcName(Request $request){
        
        $output = DB::table('ic_master')
            ->select('ic_id as value', 'ic_name as label')
            ->get();
        
        return response()->json([
            'status' => 200,
            'message' => "IC Name",
            'data' => $output
        ]);
    }

    public function getPolicyType(Request $request){
        
        $output = DB::table('policy_type_master')
            ->select('type_id as value', 'policy_type_name as label')
            ->get();
        
        return response()->json([
            'status' => 200,
            'message' => "Policy Type",
            'data' => $output
        ]);
    }

    public function getPolicyCategory(Request $request){
        
        $output = DB::table('policy_category')
            ->select('category_id as value', 'category_name as label')
            ->get();

        return response()->json([
            'status' => 200,
            'message' => "Policy Category",
            'data' => $output
        ]);
    }

    public function getSellerUsername(Request $request)
    {
        $mongoData = MongoModel::select('seller_username','trace_id as value')->where('seller_type',$request->seller_type)->where('seller_username', 'regex', '/.*' . $request->seller_username . '.*/i')->get();
 
        $formatedData = [];

        foreach($mongoData as $data){
            $formatedData[] = [
                "label" => $data->seller_username,
                "value" => $data->id
            ];
        }

        if(!empty($formatedData)){
            return response()->json([
                'status' => 200,
                'message' => "seller username found",
                'data' => $formatedData
            ]);
        }else{
            return response()->json([
                'status' => 500,
                'message' => "NO seller username found",
                'data' => $formatedData 
            ]);
        }
  
    }

    public function getSellerDetails(Request $request)
    {
        $mongoData = MongoModel::select('seller_email', 'seller_id', 'seller_mobile', 'seller_name', 'seller_username','seller_business_type','seller_business_code')->where('seller_username', $request->seller_username)->first();

        if (!empty($mongoData)) {
            return response()->json([
                'status' => 200,
                'message' => "seller details found",
                'data' => $mongoData
            ]);
        } else {
            return response()->json([
                'status' => 500,
                'message' => "NO seller details found",
                'data' => $mongoData ?? null
            ]);
        }
    }
    
}
