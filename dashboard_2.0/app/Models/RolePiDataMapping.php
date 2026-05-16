<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class RolePiDataMapping extends Model
{
    protected $table = 'role_pi_data_mapping';

    protected $fillable = [
        'module_id',
        'field_name',
        'is_enabled',
        'mask_type',
        'mask_scope',
        'mask_formula'
    ];
}
