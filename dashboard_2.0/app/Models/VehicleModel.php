<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;
use Spatie\Activitylog\Traits\LogsActivity;

class VehicleModel extends BaseModel
{
    use HasFactory, SoftDeletes;

    protected  $table = 'vehicle_type';
    protected  $fillable = [
        'name'

    ];
    protected  $logAttributes = [
        'name'
    ];

}
