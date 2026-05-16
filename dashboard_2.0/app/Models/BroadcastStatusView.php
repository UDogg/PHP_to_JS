<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class BroadcastStatusView extends Model
{
    use HasFactory;

    protected $table = 'broadcast_view_status';
    protected $fillable=[
        'broadcast_id',
        'user_id',
        'last_shown_date'
    ];
}
