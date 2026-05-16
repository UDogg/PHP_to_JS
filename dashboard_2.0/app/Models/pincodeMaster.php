<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class pincodeMaster extends Model
{
    use HasFactory, SoftDeletes;
    protected $table = 'pincode_masters';
    protected $primaryKey = 'pincode_id';

    protected $fillable = [
        'pincode',
        'country_code',
        'state_id',
        'city_id',
        'area',
        'latitude',
        'longitude',
        'geospatial_accuracy',
        'sequence'

    ];
}
