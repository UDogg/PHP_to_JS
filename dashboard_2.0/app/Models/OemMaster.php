<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class OemMaster extends Model
{
    use HasFactory,SoftDeletes;

    protected $fillable = [
        'oem_name',
        'misp_name',
        'pan_number',
        'zone',
        'gstin',
        'dealer_code',
        'branch_name',
        'address',
        'head_office',
        'misp_code',
        'pin_code',
        'city',
        'state',
        'mob_no',
        'email',
        'status',
    ];
}
