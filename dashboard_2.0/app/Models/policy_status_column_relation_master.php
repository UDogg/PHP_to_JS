<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class policy_status_column_relation_master extends Model
{
    use HasFactory;
    protected $table = 'policy_status_column_relation_masters';

    protected $fillable = [
        'column_id',
        'user_id',
        'role_id',
        'status',
        'data_sequence',
        'updated_at'
    ];
}
