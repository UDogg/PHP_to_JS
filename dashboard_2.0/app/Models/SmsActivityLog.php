<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SmsActivityLog extends Model
{
    use HasFactory;
    protected $table = 'sms_activity_logs';
    protected $fillable = [
        'mobile',
        'message',
        'type',
        'status',
        'sent_at',
        'user_id',

    ];
}
