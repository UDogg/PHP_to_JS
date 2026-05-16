<?php

namespace App\Jobs;

use App\Models\ExcelDownloadLog;
use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Foundation\Bus\Dispatchable;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Queue\SerializesModels;
use Illuminate\Support\Facades\Storage;
use Maatwebsite\Excel\Facades\Excel;
use ZipArchive;
use App\Exports\UsersExport;
use Illuminate\Support\Facades\Bus;
use Illuminate\Bus\Batch;
use Illuminate\Support\Carbon;
use App\Models\MongoModel;
use Illuminate\Support\Facades\Log;
use App\Mail\ExcelBatchMail;
use App\Models\DataExportLog;
use Illuminate\Support\Facades\Mail;
use Throwable;

class fetchExcelData implements ShouldQueue
{
    use Dispatchable, InteractsWithQueue, Queueable, SerializesModels;

    protected $queryParameters, $user_details;

    public function __construct(array $queryParameters, $user_details)
    {
        $this->queryParameters = $queryParameters;
        $this->user_details = $user_details;
    }

    public function handle()
    {
        $queryParameters = $this->queryParameters;
        $user_details = $this->user_details->toArray();
        $email = credential_decrypt($user_details['email']);
        $folder = getUUID();
        $files = [];
        $index = 1;
        $zipFileName = 'PolicyStatusExport-' . time() . '.zip';
        $zipPath = storage_path('app/' . $zipFileName);
        $zip = new ZipArchive();
        if ($zip->open($zipPath, ZipArchive::CREATE) === TRUE) {
//             MongoModel::chunk(2000, function ($data) use (&$index, &$files, $folder, &$zip) {
//                 $dataArray = $data->toArray();
// //                dd($dataArray);

//                 $excelFileName = $folder . '/file-' . $index . '-' . time() . '.xlsx';
//                 Excel::store(new UsersExport($dataArray), $excelFileName, 'public');

//                 $fileContent = Storage::disk('public')->get($excelFileName);
//                 $zip->addFromString(basename($excelFileName), $fileContent);

//                 Storage::disk('public')->delete($excelFileName);
//                 $index++;
//             });

        $page = 1;
        $perPage = 2000;

        do {
            $data = MongoModel::skip(($page - 1) * $perPage)->take($perPage)->get();

            if ($data->isEmpty()) {
                break;
            }

            $dataArray = $data->toArray();
            $excelFileName = $folder . '/file-' . $index . '-' . time() . '.xlsx';

            Excel::store(new UsersExport($dataArray), $excelFileName, 'public');

            $fileContent = Storage::disk('public')->get($excelFileName);
            $zip->addFromString(basename($excelFileName), $fileContent);

            Storage::disk('public')->delete($excelFileName);

            $index++;
            $page++;
        } while (true);

            $zip->close();
        }

        $zipUrl = url("storage/exports/{$zipFileName}");
        $uid = getUUID();
        $url = route('PolicyReportDownload',['uid' => $uid]);
        Storage::deleteDirectory($folder);

        DataExportLog::create([

            'uid'   => $uid,
            'user_id' => $user_details['id'],
            'request' => "",
            'file' => $zipFileName,
            'source' => 'job',
            'status' => 'initiated',
            'file_expiry' => Carbon::now()->addDays(config('PolicyStatusExport.fileExpiry.days'))->format('Y-m-d H:i:s'),
        ]);
        $excelreportlog = ExcelDownloadLog::where('status','0')->where('source','Misp Template Report Export')->update(['status' => '2','file_name' => $zipFileName,'updated_at' => Carbon::now()]);

//        Mail::to($email)->send(new ExcelBatchMail($url , $uid ));
//        Storage::disk(config('filesystems.default'))->put($zipFileName, file_get_contents(storage_path($zipFileName)));
//        unlink(storage_path($zipFileName));
    }

}
