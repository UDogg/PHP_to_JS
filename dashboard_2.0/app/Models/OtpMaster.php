<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class OtpMaster extends BaseModel
{
    use HasFactory;
    protected $table = 'otps_master';
    protected $primaryKey = 'otp_id';
    protected $guarded = ['otp_id'];
    protected $fillable = [
        'otp_validation_time',
        'resend_otp_time',
        'broker_name',
    ];
    protected $logAttributes = [
        'otp_validation_time',
        'resend_otp_time',
        'broker_name',
    ];
}
