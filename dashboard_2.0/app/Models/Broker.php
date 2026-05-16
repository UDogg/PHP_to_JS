<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class Broker extends BaseModel
{
    use HasFactory;
    protected $table = 'broker';
    protected $primaryKey = 'broker_id';
    protected $fillable = [
        'broker_name',
        'category',
        'cin_no',
        'address',
        'contact_no',
        'email',
        'irdia_registration_no',
        'favicon_icon',
        'logo',
        'sign_in_option',
        'status',
        'captacha_configure',
        'is_email',
        'is_sms',
        'default_otp',
        'master_otp',
    ];
    protected $logAttributes = [
        'broker_name',
        'category',
        'cin_no',
        'address',
        'contact_no',
        'email',
        'irdia_registration_no',
        'favicon_icon',
        'logo',
        'sign_in_option',
        'status',
        'is_email',
        'is_sms',
        'default_otp',
        'master_otp',
    ];
}
