<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class MispBranch extends Model
{
    use HasFactory;
    protected $table = 'misp_branches';
    protected $primaryKey = 'branch_id';
    protected $fillable = [
        'oem_id',
        'oem_name',
        'misp_id',
        'misp_name',
        'branch_name',
        'address',
        'city',
        'state',
        'pin_code',
        'code'
    ];
}
