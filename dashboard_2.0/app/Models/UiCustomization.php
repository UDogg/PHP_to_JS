<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class UiCustomization extends BaseModel
{
    use HasFactory;
    protected $table = 'ui_customizations';
    protected $primaryKey = 'placeholder_id';
    protected $guarded = ['placeholder_id'];
    protected $fillable = [
        'username',
        'password',
        'broker_name',
        'otp',
        'totp',
        'captcha',
    ];
    protected $logAttributes = [
        'username',
        'password',
        'broker_name',
        'otp',
        'totp',
        'captcha',
    ];
}
