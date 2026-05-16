<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class MaskConfigurationMaster extends Model
{
    protected $table = 'mask_configuration_master';
    protected $fillable = [
        'module_name',
        'role',
        'usertype',
        'status'
    ];
}
