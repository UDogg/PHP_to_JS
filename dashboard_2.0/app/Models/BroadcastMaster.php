<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class BroadcastMaster extends Model
{
    use HasFactory;

    protected $table = 'broadcast_module_changes';

    protected $fillable = [
        'broadcast_name',
        'user_type',
        'category',
        'content_type',
        'title',
        'description',
        'link',
        'image',
        'choose_role',
        'priority',
        'from_date',
        'to_date',
        'status',
    ];

}
