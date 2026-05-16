<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class MisReportConfigurator extends BaseModel
{
    use HasFactory;
    protected $table = 'mis_report_configurator';
    protected $primaryKey = 'mis_report_configurator_id';
    protected  $fillable = [
        'lob_id',
        'role_id',
        'status_id',
        'template_name',
        'columns',
        'new_columns',
        'sequence',
        'status',
        'static_columns',
        'stage_name'
    ];
    protected  $logAttributes = [
        'lob_id',
        'role_id',
        'status_id',
        'template_name',
        'columns',
        'new_columns',
        'sequence',
        'status',
        'static_columns',
         'stage_name'
    ];
}
