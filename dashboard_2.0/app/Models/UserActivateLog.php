<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class UserActivateLog extends Model
{
    use SoftDeletes;

    protected $fillable = [
        'activated_user_id',
        'activated_by',
        'recorded_ids',
    ];
}
