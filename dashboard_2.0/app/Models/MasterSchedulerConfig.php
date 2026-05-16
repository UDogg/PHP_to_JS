<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class MasterSchedulerConfig extends BaseModel
{
    use HasFactory;
    protected $table = 'master_scheduler_config';
    protected $primaryKey = 'id';
    protected  $fillable = [
        'scheduler_name',
        'template_name',
        'frequency',
        'starts_on',
        'ends_on',
        'user_type',
        'based_on',
        'roles',
        'schedule_time',
        'report_start_date',
        'report_end_date',
    ];

}
