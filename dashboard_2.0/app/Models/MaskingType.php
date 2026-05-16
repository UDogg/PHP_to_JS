<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class MaskingType extends Model
{
    protected $table = 'masking_type';
    protected $fillable = [
        'mask_name',
        'mongo_key'
    ];
}
