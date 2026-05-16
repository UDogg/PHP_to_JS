<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class GroupingReportKeyUtility extends BaseModel
{
    use HasFactory,SoftDeletes;
    protected $table = 'key_utility_report';
    protected $primaryKey = 'key_utility_report_id';
    protected $fillable = [
        'key',
        'key_utility_id'
    ];
    protected $logAttributes = [
        'key',
        'Key_utility_id'
    ];
}
