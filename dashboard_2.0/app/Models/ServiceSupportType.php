<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class ServiceSupportType extends BaseModel
{
    use HasFactory;
    protected $primaryKey = 'sst_id';
    protected  $table = 'service_support_types';
    protected  $fillable = [
        'service_support_type',

    ];
    protected  $logAttributes = [
        'service_support_type',

    ];
}
