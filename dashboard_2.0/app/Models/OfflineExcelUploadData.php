<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class OfflineExcelUploadData extends BaseModel
{
    use HasFactory;
    protected $table = 'offline_excel_upload_data';
    protected $primaryKey = 'offline_excel_upload_data_id';
    protected  $fillable = [
        'excel_file_name',
        'excel_data',
        'total_record',
        'failed_record',
        'success_record'
    ];
    protected  $logAttributes = [
        'excel_file_name',
        'excel_data',
        'total_record',
        'failed_record',
        'success_record'
    ];
}
