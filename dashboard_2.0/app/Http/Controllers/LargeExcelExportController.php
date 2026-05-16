<?php

namespace App\Http\Controllers;

use App\Models\ExcelDownloadLog;
use Illuminate\Support\Facades\Storage;
use Rap2hpoutre\FastExcel\FastExcel;

class LargeExcelExportController extends Controller
{
    //
    public function __construct()
    {

    }
    public function ExcelExportLarge($model,$selectColumns,$headings,$source,$filepth)
    {
        ExcelDownloadLog::where('status','0')->where('source',$source)->update(['status'=>'1','file_name'=>$filepth]);
        
        if(config('dashboard_storage_disk') === 's3'){
            $path = Storage::disk('s3')->temporaryUrl($filepth, now()->addMinutes(30));
        }else{
            $path = Storage::disk('public')->path($filepth);
        }

        (new FastExcel($this->ExcelGenerator($model,$selectColumns,$headings)))->export($path);
    }
    public function ExcelGenerator($model,$selectColumns,$headings): \Generator
    {
        $cursor = $model::query();
 
        if(!empty($selectColumns)){
           $cursor = $cursor->select($selectColumns);
        }
        $cursor = $cursor->cursor();
        foreach ($cursor as $data) {
            $row = [];
            $data = $this->DecryptionData($model,$data);
            foreach ($selectColumns as $index => $column) {
                $heading = $headings[$index] ?? $column;
                $row[$heading] = $data->$column;
            }
            yield $row;
        }
    }
    public function DecryptionData($model,$data)
    {
        $columnNeedDecryption = ['name','middle_name','last_name','dob','license_start_date','license_end_date','email','username','mobile','address','pincode','pan_no','adhar_no','bank_branch','bank_city','bank_name','account_no','ifsc_code','account_holder_name'];
        if($model == 'App\Models\User')
        {
            $columns = array_keys($data->getAttributes());
            foreach ($columns as $column)
            {
                if(in_array($column,$columnNeedDecryption))
                {
                    $data->$column = credential_decrypt($data->$column);
                }
            }
        }

        return $data;
    }


}
