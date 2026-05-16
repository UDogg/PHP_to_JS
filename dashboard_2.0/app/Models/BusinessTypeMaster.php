<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class BusinessTypeMaster extends Model
{
    protected $table = 'business_type';

    protected $fillable = [
        'name'
    ];
}
