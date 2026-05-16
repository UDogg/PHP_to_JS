<?php
namespace App\Http\Controllers;

use App\Exports\UsersExport;
use App\Exports\ReportExport;
use App\Models\MisReportConfigurator;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Storage;
use Maatwebsite\Excel\Facades\Excel;
use App\Jobs\fetchExcelData;
use Illuminate\Support\Facades\Auth;
use Symfony\Component\HttpFoundation\Response;
use App\Models\DataExportLog;
use Carbon\Carbon;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Response as Download;
use Rap2hpoutre\FastExcel\FastExcel;
class DataExportController extends Controller
{
    public function export($dataQuery, $columns, $tempId, $queryStartDate, $queryEndDate)
    {
        try {
            // $fileName = "exports/export_temp_{$tempId}_" . now()->format('Ymd_His') . ".csv";
            if ($tempId) {
                
                        $templateName = MisReportConfigurator::where('mis_report_configurator_id', $tempId)
                            ->value('template_name');
                        $fileName = Str::slug($templateName) . '_' . rand(10, 99) . '.csv';
                    } else {
                        $fileName = 'Excel_Report_' . now()->format('Ymd_His') . '.csv';
                    }
                    if(config('dashboard_storage_disk') === 's3'){
                       
                        $handle = fopen('php://temp', 'w+');

                        $s3Root = trim(env('AWS_ROOT'), '/'); 

                        $filePath = $s3Root . '/dashboard/storage/exports/' . $fileName;
                    }else{
                        $filePath = storage_path("app/public/{$fileName}");

                        if (!file_exists(dirname($filePath))) {
                            mkdir(dirname($filePath), 0755, true);
                        }

                        $handle = fopen($filePath, 'w');
                    }

        
            // Write CSV headers
            fputcsv($handle, $columns);
            if($dataQuery->count()==0) {
                $data_mis = mis_customer_renewal_popup([],$queryStartDate, $queryEndDate, $columns);
                if(count($data_mis)>0){
                    $rowsArray = $data_mis;
                }
                $rowsArray = applyMasking($rowsArray, 'excel');
                foreach ($rowsArray as $item) {
            
                    $row = [];
                    foreach ($columns as $col) {
                        $value = data_get($item, $col, '');
        
                        if (is_array($value) || is_object($value)) {
                            $value = json_encode($value);
                        }
        
                        $row[] = $value;
                    }
        
                    fputcsv($handle, $row);
                }
            }
            
            // Write data in chunks
            $dataQuery->chunk(7000, function ($rows) use ($handle, $columns, $queryStartDate, $queryEndDate) {

                if (config('mis_column_reporting_details') == "true" ||
                    config('mis_column_value_replace') == "true") {
            
                    $rowsArray = $rows->map(function ($item) {
                        return $item->toArray();
                    })->toArray();    
            
                    if (config('mis_column_value_replace') == "true") {
                        $rowsArray = mis_replace_values($rowsArray);
                    }
            
            
                    if (config('mis_column_reporting_details') == "true") {
                        $rowsArray = mis_reporting_data($rowsArray, $columns);
                    }

                    $data_mis = mis_customer_renewal_popup([],$queryStartDate, $queryEndDate, $columns);
                    if(count($data_mis)>0){
                        $rowsArray = $data_mis;
                    }
            
                    $rowsArray = applyMasking($rowsArray, 'excel');

                    foreach ($rowsArray as $item) {
            
                        $row = [];
                        foreach ($columns as $col) {
                            $value = data_get($item, $col, '');
            
                            if(in_array($col, [
                                "trace_id","policy_no","proposal_no",
                                "previous_policy_number","tp_policy_number"
                            ])) {
                                $value = "'".$value;
                            }
            
                            if (is_array($value) || is_object($value)) {
                                $value = json_encode($value);
                            }
            
                            $row[] = $value;
                        }
            
                        fputcsv($handle, $row);
                    }
            
                } else {
                    $data_mis = mis_customer_renewal_popup([],$queryStartDate, $queryEndDate, $columns);
                    if(count($data_mis)>0){
                        $rows = $data_mis;
                    }
                    $rows = collect($rows)->map(function ($item) {
                        return is_object($item) && method_exists($item, 'toArray')
                            ? $item->toArray()
                            : (array) $item;
                    })->toArray();

                    $rows = applyMasking($rows, 'excel');
            
                    foreach ($rows as $item) {
            
                        $row = [];
                        foreach ($columns as $col) {
                            $value = data_get($item, $col, '');
            
                            if(in_array($col, [
                                "trace_id","policy_no","proposal_no",
                                "previous_policy_number","tp_policy_number"
                            ])) {
                                $value = "'".$value;
                            }
            
                            if (is_array($value) || is_object($value)) {
                                $value = json_encode($value);
                            }
            
                            $row[] = $value;
                        }
            
                        fputcsv($handle, $row);
                    }
                }
            });

            if(config('dashboard_storage_disk') === 's3'){

                rewind($handle);

                $uploaded = Storage::disk('s3')->writeStream(
                    $filePath,
                    $handle
                );
                
                if (is_resource($handle)) {
                    fclose($handle);
                }
                
                if (!$uploaded) {
                    throw new \Exception('S3 upload failed');
                }
                                
                if (!Storage::disk('s3')->exists($filePath)) {
                        throw new \Exception('File not found in S3 after upload');
                    }
                 
                $downloadUrl = Storage::disk('s3')->temporaryUrl(
                    $filePath,
                    now()->addMinutes(30)
                );

            }
            else
            { 
                if (is_resource($handle)) {
                    fclose($handle);
                }
                $downloadUrl = Storage::disk('public')->url($fileName);
            }

            // Log the export
            DataExportLog::create([
                'uid' => getUUID(),
                'user_id' => auth()->id(),
                'request' => '', // Add request data if needed
                'file' => $fileName,
                'source' => 'MIS Report Download',
                'status' => 'completed',
                'file_expiry' => now()->addDays(config('PolicyStatusExport.fileExpiry.days', 7)),
            ]);

            return [
                'status' => 'success',
                'message' => 'File is ready for download.',
                'download_link' => $downloadUrl,
            ];

        } catch (\Throwable $e) {
            return [
                'status' => 'pending',
                'Message' => 'Export failed or will be processed via email.',
                'error' => $e->getMessage(),
            ];
        }
    }
    private function getQueryParameters($query)
    {
        return $query->getQuery()->wheres;
    }

    private function countRecords($query)
    {
        return $query->count();
    }

    private function retrieveData($query)
    {
        // return $query->get()->toArray();
        return $query->cursor(); // returns a generator

    }

    public function validateFile($uid)
    {
        $fileDetails = DataExportLog::select('file_expiry', 'file')->where('uid', $uid)->first();

        if (!empty($fileDetails)) {
            if ($fileDetails[ 'file_expiry' ] >= now()) {
                if (Storage::disk(config('filesystems.default'))->exists($fileDetails[ 'file' ])) {
                    $headers = [
                        'Content-Type' => 'Content-Type: application/zip',
                        'Content-Disposition' => 'attachment; filename=' . $fileDetails[ 'file' ]
                    ];
                    return Download::make(Storage::disk(config('filesystems.default'))->get($fileDetails[ 'file' ]), Response::HTTP_OK, $headers);

                } else {
                    return "File is no longer available.";
                }
            } else {
                return "File is expired";
            }
        } else {
            return "Invalid URL. ";
        }
    }
}
