<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class CorporateUserWhitelisting extends Model
{
    protected $table = 'corporate_user_whitelisting';

    protected $fillable = [
        'corporate_id',
        'email',
        'mobile',
        'status',
        'otp',
        'otp_sent_at',
        'failed_login_attempts',
        'lockout_time',
    ];

    protected $casts = [
        'otp_sent_at' => 'datetime',
        'lockout_time' => 'datetime',
    ];
}
