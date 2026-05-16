<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class substagemaster extends BaseModel
{
    use HasFactory;
    protected  $table = 'sub_stage_master';
    protected  $fillable = [
        'sub_stage_name',
        'is_renewal',
    ];
    protected  $logAttributes = [
        'sub_stage_name',
        'is_renewal',
    ];
}
