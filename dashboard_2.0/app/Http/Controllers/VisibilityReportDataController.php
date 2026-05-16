<?php

namespace App\Http\Controllers;

use App\Exports\VisibilityReportExportData;
use App\Exports\VisibilitySuccessFailureReportExport;
use Illuminate\Http\Request;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Support\Facades\Storage;
use Maatwebsite\Excel\Facades\Excel;
use App\Services\ThirdPartyTokenService;
use Illuminate\Support\Facades\Auth;
use Str;

use App\Models\ExcelDownloadLog;
use App\Jobs\ExportLargeExcel;
use App\Models\VisibilityReportDownloadReport;
class VisibilityReportDataController extends Controller
{
    public function visibilityReportData(Request $request, ThirdPartyTokenService $tokenService)
    {
        $auth = Auth::user();
        $editPermission = "Visibility Report.edit";
        if(!$auth->can($editPermission)) {
            return response()->json([
                'success' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }
        
        $request->validate([
            'section' => 'required|in:health,motor',
            'from' => 'required|date',
            'to' => 'required|date',
            'methods' => 'required',
        ]);

        $section = $request->input('section');
        $from = date("Y-m-d\\TH:i:s\\Z", strtotime($request->input('from')." 00:00:00"));
        $to = date("Y-m-d\\TH:i:s\\Z", strtotime($request->input('to')." 23:59:59"));
        $requestType = $request->input('methods'); 
        $url = config("visibilityReport_{$section}");

        if (!$url) {
            return response()->json([
                'success' => false,
                'message' => 'Invalid section or URL not found.',
            ], 400);
        }

        $methods = ($requestType == 'all_methods') ? ['quote', 'ckyc', 'proposal'] : [$requestType];

        $token = $tokenService->getToken($url);
        $queryParams = [
            'from' => $from,
            'to' => $to,
            'methods' => $methods,
        ];

        
        $client = new Client();
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Validation' => $token,
            'Origin' => request()->headers->get('origin')
        ];
        $methodType = 'GET';

        $jsonBody = json_encode($queryParams);

        try {
            $response = $client->request('GET', $url, [
                'headers' => $headers,
                'query' => $queryParams,
            ]);
            $responseData = json_decode($response->getBody(), true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $url,
                    $methodType,
                    $queryParams,
                    $responseData,
                    $response->getStatusCode(),
                    $headers
                );
            }

            $filteredData = $this->filterResponseData($responseData, $requestType);

            if ($request->filled('export') && $request->input('export') == true) {
                $exportData = [];
                $specificData = $filteredData[$request->specificExportType] ?? [];
                if ($request->success_or_failure == 'success') {

                    foreach ($specificData as $data) {
                        $headings = ['IC Name', 'IC Success Count', 'Average Response Time'];
                        $exportData[] = [
                            'IC Name' => $data['company_name'],
                            'IC Success Count' => $data['success'],
                            'Average Response Time' => (string) $data['success_average_response_time'],
                        ];
                    }
                } else if ($request->success_or_failure == 'failure') {
                    foreach ($specificData as $data) {
                        $headings = ['IC Name', 'IC Failure Count', 'Average Response Time'];
                        $exportData[] = [
                            'IC Name' => $data['company_name'],
                            'IC Failure Count' => $data['failure'],
                            'Average Response Time' => (string)$data['failure_average_response_time'],
                        ];
                    }
                }

                $fileName = 'visibility_success_failure_report_' . rand(100000, 999999) . '.xlsx';
                $filePath = 'exports/' . $fileName;
                $dataCount = count($exportData);
                $randomstring = Str::random(10);
                $filePath = 'exports/visibility_report_' . $randomstring . '.xlsx';

                if ($dataCount > config('DATA.EXPORT.LIMIT')) {

                    VisibilityReportDownloadReport::insert([
                        'user_id' => $auth->id,
                        'file_name' => $fileName,
                        'request' => json_encode($request->all()),
                        'status' => '0',
                        'created_at' => now(),
                        'source' => 'Visibility Report Export',
                    ]);

                    ExportLargeExcel::dispatch(
                        null, 
                        $headings,
                        $exportData,
                        $auth->id,
                        'Visibility Report Export',
                        $filePath,
                        null 
                    )->onQueue('LargeExcelExports');

                    return response()->json([
                        'status' => 200,
                        'message' => 'Data is too large. Added to queue, download later from job list.',
                    ]);
                }

                if(config('dashboard_storage_disk') === 's3') $donwloadFrom = 's3';
                else $donwloadFrom = 'public';

                Excel::store(new VisibilitySuccessFailureReportExport($exportData, $headings), $filePath, $donwloadFrom);

                if(config('dashboard_storage_disk') === 's3'){
                    $downloadLink = Storage::disk('s3')->temporaryUrl($filePath, now()->addMinutes(30));
                }else{
                    $downloadLink = Storage::url($filePath);
                }

                return response()->json([
                    'success' => true,
                    'download_link' => url($downloadLink),
                ]);
            }

            return response()->json(
                $filteredData,
            );
        } catch (\Exception $e) {

            if(config('store_api_logs') == true){
                logApiRequestResponse(
                    $url,
                    $methodType,
                    $queryParams,
                    $e->getMessage() ?? null,
                    $e->getCode() ?? null,
                    $headers
                );
            }
            return response()->json([
                'success' => false,
                'message' => 'Error fetching data',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    /**
     * Filter the response data based on the requested method type.
     *
     * @param array $responseData
     * @param string $requestType
     * @return array
     */
    private function filterResponseData(array $responseData, string $requestType): array
    { 
      
            $result = [];
            // Looping to get dynamic type from responseData eg: proposal,quote,ckyc etc
            foreach ($responseData['companies'] as $companyData) {
                if (isset($companyData['methods'])) {
                    foreach ($companyData['methods'] as $type => $methodData) {
                        if (!isset($result[$type])) {
                            $result[$type] = [];
                        }
                    }
                }
            }

            // Now proceed to process the data as before
            foreach ($responseData['companies'] as $companyName => $companyData) {
                if (isset($companyData['methods'])) {
                    foreach ($companyData['methods'] as $type => $methodData) {
                         // Calculate the success and failure percentages with two decimal places
                        $successPercentage = number_format(($methodData['success'] / $methodData['total']) * 100, 2);
                        $failurePercentage = number_format(($methodData['failure'] / $methodData['total']) * 100, 2);
                        $result[$type][] = [
                            'success' => $methodData['success'] . " of " . $methodData['total'] . " (" . $successPercentage . '%)',
                            'failure' => $methodData['failure'] . " of " . $methodData['total'] . " (" . $failurePercentage . '%)',
                            'total' => $methodData['total'],
                            'average_response_time' => $methodData['average_response_time'],
                            'success_average_response_time' => $methodData['success_average_response_time'],
                            'failure_average_response_time' => $methodData['failure_average_response_time'],
                            'company_name' => $companyName,
                        ];
                    }
                }
            }

            return $result;

           
        }
    


    public function visibilityReportDetails(Request $request, ThirdPartyTokenService $tokenService)
    {
        $auth = Auth::user();
        $editPermission = "Visibility Report.edit";
        if(!$auth->can($editPermission)) {
            return response()->json([
                'success' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }
        
        $request->validate([
            'section' => 'required|in:health,motor',
            'from' => 'required|date',
            'to' => 'required|date',
            'page' => 'required|integer',
            'per_page' => 'required|integer',
            'type' => 'required|string',
            'error_types' => 'required|string', 
            'company_aliases' => 'nullable|string' 
        ]);

        $section = $request->input('section');
        $from=strtotime(date($request->input('from'))." 00:00:00");
        $to=strtotime(date($request->input('to'))." 23:59:59");
        $page = $request->input('page');
        $per_page = $request->input('per_page');
        if($request->filled('export') && $request->input('export') == 'true'){
            $page = 1;  
            $per_page = $request->input('total_records');
        }
        $type = $request->input('type');
        $requestType[] = $request->input('error_types');
        $company_aliases = $request->input('company_alias');

        $url = config("visibilityDataDetail_{$section}");

        if (!$url) {
            return response()->json([
                'success' => false,
                'message' => 'Invalid section or URL not found.',
            ], 400);
        }

        $error_types = ($requestType == 'all_error_types') ? 'quote_success' : $requestType;
        $company_aliases = (is_null($company_aliases) || strtolower($company_aliases) == 'all') ? null : $company_aliases;
        $token = $tokenService->getToken($url);

        $headers = [
            'Content-Type' => 'application/json',
            'Validation' => $token,
        ];
        $methodType = 'GET';

        $queryParams = [
            'from' =>$from,
            'to' => $to,
            'page' => $page,
            'per_page' => $per_page,
            'type' => $type,
            'error_types' => $error_types,
            'company_aliases' => [$company_aliases],
        ];
        $client = new Client(); 

        try {
            $response = $client->request($methodType, $url, [
                'headers' => $headers,
                'query' => $queryParams,
            ]);

            $responseData = json_decode($response->getBody(), true);
            if(config('store_api_logs') == true && $request->has('export') == false){
    
                logApiRequestResponse(
                    $url,
                    $methodType,
                     $queryParams, 
                     $responseData,
                    $response->getStatusCode(),
                    $headers
                );
            }

            if ($request->filled('export') && $request->input('export') == 'true') {
       
                $data = $responseData['data'] ?? [];
                $dataCount = count($data);
                $columns = array_keys($data[0]);

                $icName = $data[0]['ic_name'] ?? 'report';
                $randomstring = Str::random(10);
                $filePath = 'exports/visibility_report_details_' . $randomstring . '.xlsx';
                $fileName = 'visibility_report_details_' . $icName . '_' . date('Y-m-d_H-i-s') . '.xlsx';

                if ($dataCount > config('DATA.EXPORT.LIMIT')) {

                    VisibilityReportDownloadReport::insert([
                        'user_id' => $auth->id,
                        'file_name' => $fileName,
                        'request' => json_encode($request->all()),
                        'status' => '1',
                        'created_at' => now(),
                        'source' => 'Visibility Report Details Export',
                    ]);

                    ExportLargeExcel::dispatch(
                        null,
                        null, 
                        $data,
                        $auth->id,
                        'Visibility Report Details Export',
                        $filePath,
                        null
                    )->onQueue('LargeExcelExports');

                    return response()->json([
                        'success' => true,
                        'message' => 'Data is too large. Added to queue, download later from job list.',
                    ]);
                }

                ExcelDataExportLog($auth->id, $filePath, 'visibilityReportDetails', 'completed', $request->all());

                if(config('dashboard_storage_disk') === 's3') $donwloadFrom = 's3';
                else $donwloadFrom = 'public';

                Excel::store(new VisibilityReportExportData($data), $filePath, $donwloadFrom);

                if(config('dashboard_storage_disk') === 's3'){
                    $downloadLink = Storage::disk('s3')->temporaryUrl($filePath, now()->addMinutes(30));
                }else{
                    $downloadLink = Storage::url($filePath);
                }
                

                return response()->json([
                    'success' => true,
                    'download_link' => url($downloadLink),
                ]);
            }
    
            return $responseData ;
        } catch (\Exception $e) {
            return response()->json([
                'success' => false,
                'message' => 'Error fetching data',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    public function getVisibilityDownloadedReport(Request $request)
    {
        $perPage = $request->input('per_page', 10); 
        $data = VisibilityReportDownloadReport::from('visibility_report_downloaded_log as v')
            ->join('users as u', 'v.user_id', '=', 'u.id')
            ->select(
                'v.user_id',
                'u.name as user_name',
                'v.source',
                'v.status',
                'v.created_at',
                'v.file_name',
                'v.request' 
            )
            ->paginate($perPage);

        $data->getCollection()->transform(function ($item, $key) use ($data, $perPage) {

            $requestData = json_decode($item->request, true);

            return [
                'sr_no'         => ($data->currentPage() - 1) * $perPage + ($key + 1),
                'template_name' => $item->file_name,
                'start_date'    => isset($requestData['to']) 
                                    ? date('d-m-Y', strtotime($requestData['to'])) 
                                    : '',
                'end_date'      => isset($requestData['from']) 
                                    ? date('d-m-Y', strtotime($requestData['from'])) 
                                    : '',
                'created_on'    => date('d-m-Y H:i:s', strtotime($item->created_at)),
                'created_by'    => !empty($item->user_name) 
                                    ? credential_decrypt($item->user_name) 
                                    : '',
                'status'        => $item->status == 0 ? 'Pending' : 'Completed',
                'actions'       => url('storage/' . $item->file_name)
            ];
        });

        $column_head_data = [
            ["header" => "Sr No","accessorKey" => "sr_no","isActions" => false,"type" => "string"],
            ["header" => "Template Name","accessorKey" => "template_name","isActions" => false,"type" => "string"],
            ["header" => "Start Date","accessorKey" => "start_date","isActions" => false,"type" => "string"],
            ["header" => "End Date","accessorKey" => "end_date","isActions" => false,"type" => "string"],
            ["header" => "Created On","accessorKey" => "created_on","isActions" => false,"type" => "string"],
            ["header" => "Created By","accessorKey" => "created_by","isActions" => false,"type" => "string"],
            ["header" => "Status","accessorKey" => "status","isActions" => false,"type" => "string"],
        ];

        return response()->json([
            'success' => true,
            'column_head' => $column_head_data,
            'return_data' => $data->items(),
            'pagination' => [
                'current_page' => $data->currentPage(),
                'last_page'    => $data->lastPage(),
                'per_page'     => $data->perPage(),
                'total'        => $data->total(),
            ],
            'message' => 'Visibility Report Downloaded Report fetched successfully',
        ]);
    }

}
