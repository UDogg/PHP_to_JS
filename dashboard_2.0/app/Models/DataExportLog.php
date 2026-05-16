<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class DataExportLog extends BaseModel
{
    use HasFactory;
    protected $table = 'data_export_log';

    protected $fillable = [
        'uid',
        'user_id',
        'request',
        'file',
        'source',
        'status',
        'file_expiry',
    ];

}
