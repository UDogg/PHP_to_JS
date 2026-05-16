<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class UserDeactivateCounter extends Model
{
    use SoftDeletes;

    protected $fillable = [
        'user_id',
        'deactivate_counter',
        'deactivate_status',
    ];
}
