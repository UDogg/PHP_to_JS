<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class cityMaster extends Model
{
    use HasFactory,SoftDeletes;
    protected $table = 'city_masters';
    protected $primaryKey = 'city_id';

    protected $fillable = [
        'zone_id',
        'state_id',
        'city_name',

    ];
}
