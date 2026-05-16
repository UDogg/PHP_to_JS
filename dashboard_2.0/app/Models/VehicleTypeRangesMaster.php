<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class VehicleTypeRangesMaster extends Model
{
    protected  $table = 'vehicle_type_ranges';

    protected  $fillable = [
        'range_type_id',
        'vehicle_type_id',
        'range' 
    ];
}
