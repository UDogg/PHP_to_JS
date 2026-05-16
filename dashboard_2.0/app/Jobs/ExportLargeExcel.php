<?php

namespace App\Jobs;

use App\Exports\AllDataExport;
use App\Http\Controllers\LargeExcelExportController;
use App\Mail\ExcelBatchMail;
use App\Mail\UserExcelReady;
use App\Models\ExcelDownloadLog;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Foundation\Bus\Dispatchable;
use Illuminate\Foundation\Queue\Queueable;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Queue\SerializesModels;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\Storage;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Mail;


class ExportLargeExcel implements ShouldQueue
{
    use Queueable, Dispatchable, InteractsWithQueue, SerializesModels;

    /**
     * Create a new job instance.
     */
    private $headings;
    private $queryColumns;
    private $request;
    private $userId;
    private $source;
    private $model;
    private  $filepath;
    public function __construct($model,$headings, $request,$userId,$source,$filepath,$queryColumns)
    {
        $this->request = $request;
        $this->headings = $headings;
        $this->userId = $userId;
        $this->source = $source;
        $this->model = $model;
        $this->filepath = $filepath;
        $this->queryColumns = $queryColumns;
    }

    /**
     * Execute the job.
     */
    public function handle(): void
    {
    
        Log::info('Memory usage before export: ' . memory_get_usage());
        $largeExcelExportControler = new LargeExcelExportController;
        
        $largeExcelExportControler->ExcelExportLarge($this->model,$this->queryColumns,$this->headings,$this->source,$this->filepath);
        $current_insert=ExcelDataExportLog($this->userId,$this->filepath,$this->source,'completed',$this->request);

        ExcelDownloadLog::where('status','1')->where('source',$this->source)->update(['status'=>'2','file_name'=>$this->filepath]);
        Log::info('Memory usage after export: ' . memory_get_usage());

        // Send email 
        // $user = \App\Models\User::find($this->userId);
        // if ($user && $user->email) {
        //     Mail::to($user->email)->queue((new UserExcelReady($this->filepath))->onQueue('LargeExcelExports'));
        // }


    }
}
