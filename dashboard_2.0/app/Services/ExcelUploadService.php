<?php

namespace App\Services;

use App\Models\{OfflineExcelUploadData, lobMaster, ExcelKeyMaster, User};
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Http;
use Maatwebsite\Excel\Facades\Excel;
use PhpOffice\PhpSpreadsheet\Shared\Date;
use App\Exports\ExcelKeyExport;
use App\Jobs\PollRenewalDataJob;

class ExcelUploadService
{
    protected $dateColumns = [
        'previous_policy_start_date',
        'previous_policy_end_date',
        'previous_tp_start_date',
        'previous_tp_end_date',
        'policy_issue_date',
        'policy_start_date',
        'policy_expiry_date',
        'nominee_dob',
        'date_of_birth',
    ];

    public function processExcelUpload($request)
    {
        $lob = lobMaster::select('lob')->where('id', $request->input('lob_id'))->first();
        $lobName = $lob->lob ?? 'Unknown';
        $filename = $request->file('excel_upload')->getClientOriginalName();
        
        $excelData = $this->importExcelData($request);
        if (empty($excelData)) {
            return response()->json(["status" => 500, "message" => "No Data Found in Excel"]);
        }
        if ($excelData->has('1') && !$excelData[1]) {
            return response()->json(["status" => 500, "message" => "Column Mismatch or Invalid Excel Format"]);
        }
        
        $offlineUpload = OfflineExcelUploadData::create([
            'excel_file_name' => $filename,
            'lob_id' => $request->lob_id,
            'excel_data' => json_encode($excelData),
            'total_record' => count($excelData),
            'failed_record' => 0,
            'success_record' => count($excelData),
        ]);

        [$finalData, $errorData] = $this->mapExcelData($request, $excelData, $request->lob_id);
        
        // Handle Errors
        if (!empty($errorData)) {
            return $this->generateErrorResponse($lobName, $finalData, $offlineUpload, $errorData,$request->lob_id);
        }

        // Send Data to API
        return $this->sendDataToAPI($finalData, $lobName, $offlineUpload,$request->lob_id);
    }

    private function importExcelData($request)
    {
        $controller = new \App\Http\Controllers\OfflineExcelUpload\ExcelKeyMasterController();
        return $controller->import($request);
    }


    private function mapExcelData($request, $dataArray, $lobId)
    {
        $excelData = ExcelKeyMaster::join('policystatus_column_master', 'policystatus_column_master.id', '=', 'excel_key_master.policystatus_column_master_id')
            ->where('lob_id', $lobId)
            ->select('policystatus_column_master_id', 'column_name', 'excel_column_name')
            ->get();
        
        $columns = $excelData->pluck('column_name', 'excel_column_name')->toArray();
        $errorResult = [];
        $finalResult = [];

        foreach ($dataArray as $index => $row) {
            $mappedData = [];

            foreach ($row as $key => $value) {
                if ($key === 'Proposer Mobile No*' || $key === 'Proposer Mobile No') {
                    $mobile = trim((string)$value);
                    if (!preg_match('/^\d{10}$/', $mobile)) {
                        $mappedData['proposer_mobile_no'] = null;
                        $mappedData['Error Message'] = ($mappedData['Error Message'] ?? '') ?: '';
                        $mappedData['Error Message'] = trim($mappedData['Error Message'], " | ");
                        $mappedData['Error Message'] = ($mappedData['Error Message'] === '' ? '' : $mappedData['Error Message'] . ' | ') . 'Invalid Proposer Mobile No (must be 10 digits)';
                    } else {
                        $mappedData['proposer_mobile_no'] = $mobile;
                    }
                    continue;
                }

                if (isset($columns[$key])) {
                    $columnName = $columns[$key];

                    if (in_array($columnName, $this->dateColumns) && is_numeric($value)) {
                        $mappedData[$columnName] = Date::excelToDateTimeObject($value)->format('Y-m-d');
                    } else {
                        $mappedData[$columnName] = $value;
                    }
                }
            }

            $this->mapSellerData($mappedData, ($index-1), $errorResult);

            $finalResult[] = $mappedData;
        }

        return [$finalResult, $errorResult];
    }

    private function mapSellerData(&$mappedData, $index, &$errorResult)
    {
        if (isset($mappedData['proposer_mobile_no'])) {
            $mobile = trim((string)$mappedData['proposer_mobile_no']);
            if ($mobile === '' || !preg_match('/^\d{10}$/', $mobile)) {
                $mappedData['proposer_mobile_no'] = null;
                $mappedData['Error Message'] = ($mappedData['Error Message'] ?? '') . (empty($mappedData['Error Message']) ? '' : ' | ') . 'Invalid Proposer Mobile No (must be 10 digits)';
                $errorResult[$index] = $mappedData['Error Message'];
            }
        }

        $possibleFields = [
            'rm_code' => 'SP',
            'rm_username' => 'E',
            'pos_username' => 'P',
            'partner_username' => 'Partner'
        ];

        foreach ($possibleFields as $field => $sellerType) {
            if (!empty($mappedData[$field])) {
                $user = User::where('employee_code', $mappedData[$field])->first();

                if ($user) {
                    $mappedData['policy_row_no'] = $index;
                    $mappedData['seller_name'] = credential_decrypt($user->name);
                    $mappedData['seller_mobile'] = credential_decrypt($user->mobile);
                    $mappedData['seller_email'] = credential_decrypt($user->email);
                    $mappedData['seller_id'] = $user->id;
                    $mappedData['seller_type'] = $sellerType;
                    $mappedData['seller_username'] = credential_decrypt($user->mobile);
                    return;
                }
            }
        }

        $sellerErr = 'RM/POS/Partner details missing. Please enter any one detail.';
        $mappedData['Error Message'] = ($mappedData['Error Message'] ?? '') . (empty($mappedData['Error Message']) ? '' : ' | ') . $sellerErr;
        $errorResult[$index] = $mappedData['Error Message'];
    }

    private function generateErrorResponse($lobName, $data, $offlineUpload, $errors,$lobId=1)
    {
        $failedCount = count($errors);
        $successCount = max(0, count($data) - $failedCount);

        foreach ($errors as $key => $value) {
            $data[$key]['Error Message'] = $value;
        }

        $fileUrl = $this->storeExcelFile($lobName, $data,$lobId);

        $offlineUpload->update([
            'failed_record' => $failedCount,
            'success_record' => $successCount
        ]);

        return response()->json([
            'status' => 'error',
            'file_url' => $fileUrl,
            'total_record' => count($data),
            'failed_record' => $failedCount,
            'success_record' => $successCount,
            'data' => $data
        ]);
    }

    private function sendDataToAPI($data, $lobName, $offlineUpload,$lobId=1)
    {
        if(config('poll_renewal_data')){
            $url = $lobName=='health'?config('health-renewal-data-upload-batch'):config('renewal-data-upload-batch');
        }else{
            $url = $lobName=='health'?config('health-renewal-data-upload'):config('renewal-data-upload');
        }
        
        $headers = [
            'Content-Type' => 'application/json',
            'Origin' => request()->headers->get('origin')
        ];
        $headers = addTokenToHeader($headers, $url);

        $response = Http::timeout(60)->withHeaders($headers)->post($url, ["policies" => $data]);
        $responseData = $response->json();

        $batch_id = $responseData['data']['batch_id'] ?? null;
        $renewal_url = $responseData['data']['poll_api'] ?? null;


        if (config('store_api_logs')) {
            logApiRequestResponse($url, 'POST', $data, $responseData, $response->getStatusCode(), $headers,"excel upload");
        }

        if(config('poll_renewal_data') && $renewal_url && $batch_id){

            $offlineUpload->update([
                'batch_id' => $batch_id
            ]);
    
            PollRenewalDataJob::dispatch($renewal_url,$data,$batch_id,$offlineUpload->id,$lobName,$lobId);        
            return response()->json([
                'status' => 200,
                'message' => 'Data is too large to upload. Added to Queue. You will get update later in the job list.'
            ]);
        }else{
            $failedCount = $responseData['status'] ? 0 : (is_array($responseData['message'])?count($responseData['message']):count($data));
            $successCount = max(0, count($data) - $failedCount);
            $excelDataForError=array_values(json_decode($offlineUpload->excel_data,true));
            $processedData = $responseData['status'] ? $excelDataForError : $this->processApiErrors($responseData['message'] ?? [], $excelDataForError);
            $processedDataWithMapping = $responseData['status'] ? $data : $this->processApiErrors($responseData['message'] ?? [], $data);
    
            $fileUrl = $this->storeExcelFile($lobName, $processedData,$lobId);
    
            $offlineUpload->update([
                'failed_record' => $failedCount,
                'success_record' => $successCount
            ]);
    
            return response()->json([
                'status' => $responseData['status'] ? 'success' : 'error',
                'file_url' => $fileUrl,
                'total_record' => count($data),
                'failed_record' => $failedCount,
                'success_record' => $successCount,
                'data' => $processedDataWithMapping
            ]);
        }
    }
    private function processApiErrors($errors, $dataArray)
    {
        return collect($dataArray)->map(function ($row, $index) use ($errors) {

            if (is_array($errors)) {
            $errorMessages = collect($errors)->filter(fn($_, $key) => str_starts_with($key, "policies.$index."))->map(fn($error, $key) => str_replace("policies.$index.", '', implode(" | ", $error)))->values()->toArray();
            $row['Error Message'] = implode(" | ", $errorMessages);
            }else {
                $row['Error Message'] = $errors; 
            }
            return $row;
        })->toArray();
    }

    private function storeExcelFile($lobName, $data,$lobId=1)
    {
        $fileName = "{$lobName}_" . date('Y_m_d') . "_" . time() . ".xlsx";

        if(config('dashboard_storage_disk') === 's3') $donwloadFrom = 's3';
        else $donwloadFrom = 'public';

        Excel::store(new ExcelKeyExport($lobId,$data), $fileName, $donwloadFrom);

        if(config('dashboard_storage_disk') === 's3'){
            $fileUrl = Storage::disk('s3')->temporaryUrl($fileName, now()->addMinutes(30));
        }else{
            $fileUrl = Storage::url($fileName);
        }
        
        return $fileUrl;
    }

    function pollForResult($url)
    {
        $maxAttempts = 12; // e.g. 12 attempts
        $delaySeconds = 5; // wait 5 sec between attempts

        for ($i = 0; $i < $maxAttempts; $i++) {
            $response = Http::timeout(10)->get($url);

            if ($response->successful()) {
                $data = $response->json();

                // adjust condition based on API response
                if (isset($data['status']) && $data['status'] === 'completed') {
                    return $data;
                }
            }

            sleep($delaySeconds);
        }

        // fallback if not completed within time
        return $this->fallbackResponse();
    }

    private function fallbackResponse()
    {
        return [
            'status' => 'timeout',
            'message' => 'Processing not completed in time',
            'data' => []
        ];
    }
}
