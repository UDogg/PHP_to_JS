<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class RoleCodeMapping extends Model
{
     protected $table = 'role_code_mapping';

    protected $fillable = [
        'role_id',
        'parameter_name',
        'parameter_value',
        'status',
    ];
}


