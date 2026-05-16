<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class MispMaster extends Model
{
    use HasFactory;
    protected $table = 'misp_masters';
    protected $primaryKey = 'misp_id';
    protected $fillable = [
        'oem_name',
        'misp_name',
        'misp_code',
        'pan_number',
        'gstin',
        'zone',
        'dealer_code',
        'pin_code',
        'city',
        'state',
        'mob_no',
        'email',
        'status',
    ];
}
