<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class VisibilityReportDownloadReport extends Model
{
    protected $table = "visibility_report_downloaded_log";

    protected $fillable = [
        'user_id',
        'file_name',
        'source',
        'status',
        'request'
    ];
}
