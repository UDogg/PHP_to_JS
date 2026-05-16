<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class FuelType extends BaseModel
{
    use HasFactory,SoftDeletes;
    protected  $table = 'fuel_type';
    protected  $fillable = [
        'fuel_type'

    ];
    protected  $logAttributes = [
        'fuel_type'
    ];
}
