<?php

namespace App\Jobs;

use App\Models\OfflineExcelUploadData;
use Illuminate\Bus\Queueable;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Cache;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Foundation\Bus\Dispatchable;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Queue\SerializesModels;
use App\Exports\ExcelKeyExport;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;

class PollRenewalDataJob implements ShouldQueue
{
    use Dispatchable, InteractsWithQueue, Queueable, SerializesModels;

    protected $url;
    protected $data;
    protected $batch_id;
    protected $offlineUploadId;
    protected $lobName;
    protected $lobId;

    public $timeout = 120; 

    public function __construct($url, $data, $batch_id, $offlineUploadId, $lobName, $lobId)
    {
        $this->url = $url;
        $this->data = $data;
        $this->batch_id = $batch_id;
        $this->offlineUploadId = $offlineUploadId;
        $this->lobName = $lobName;
        $this->lobId = $lobId;
    }

    public function handle()
{
    try {
        $response = Http::timeout(10)->get($this->url);

        if ($response->successful()) {
            $responseData = $response->json();

            if (
                isset($responseData['batch_status']) &&
                $responseData['batch_status'] === 'completed'
            ) {

                $failedCount = $responseData['status']
                    ? 0
                    : (is_array($responseData['message'])
                        ? count($responseData['message'])
                        : count($this->data));

                $successCount = max(0, count($this->data) - $failedCount);

                $processedData = $responseData['status']
                    ? $this->data
                    : $this->processApiErrors(
                        $responseData['message'] ?? [],
                        $this->data
                    );

                $fileUrl = $this->storeExcelFile(
                    $this->lobName,
                    $processedData,
                    $this->lobId
                );

                OfflineExcelUploadData::where(
                    'offline_excel_upload_data_id',
                    $this->offlineUploadId
                )->update([
                    'failed_record' => $failedCount,
                    'success_record' => $successCount,
                    'file_url' => $fileUrl,
                ]);

                return;
            }
            $this->release(5);
            return;
        }

        $this->release(5);

    } catch (\Exception $e) {
        \Log::error("Polling error: " . $e->getMessage());

        $this->release(5);
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
        Excel::store(new ExcelKeyExport($lobId,$data), $fileName, 'public');
        return Storage::disk('public')->url($fileName);
    }
}