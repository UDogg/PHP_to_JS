<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class PolicyTypeMaster extends Model
{
    protected $table = 'policy_type_master';

    protected $fillable = [
        'type_id',
        'policy_type_name'
    ];
}
