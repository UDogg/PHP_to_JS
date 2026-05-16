<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class ChannelMaster extends Model
{
    protected $table = 'channel_master';

    protected $fillable = [
        'channel_name'
    ];
}
