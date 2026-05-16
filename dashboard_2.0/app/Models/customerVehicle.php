<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class customerVehicle extends Model
{
    use HasFactory,SoftDeletes;
    protected  $table = 'customer_vehicles';
    protected $primaryKey = 'customer_vehicle_id';
    protected  $fillable = [
        'vehicle_id',
        'user_id',
        'fuel_id',
        'reg_no',
        'date_of_registration',
        'make',
        'model',
        'variant',
        'versionName',
        'status'

    ];
    protected  $logAttributes = [
        'vehicle_id',
        'user_id',
        'fuel_id',
        'reg_no',
        'date_of_registration',
        'make',
        'model',
        'variant',
        'versionName',
        'status'

    ];
}
