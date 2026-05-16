<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class masterCompany extends BaseModel
{
    use HasFactory;
    use SoftDeletes;
    protected $primaryKey = 'company_id';
    protected  $table = 'master_companies';
    protected  $fillable = [

        'company_name',
        'company_shortname',
        'health_alias',
        'motor_alias',
        'url',
        'logo',
        'is_renewal',
        'is_renewal_bike',

    ];
    protected  $logAttributes = [

        'company_name',
        'company_shortname',
        'health_alias',
        'motor_alias',
        'url',
        'logo',
        'is_renewal',
        'is_renewal_bike',

    ];
}
