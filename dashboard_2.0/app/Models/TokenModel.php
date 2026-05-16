<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Spatie\Activitylog\LogOptions;
use Spatie\Activitylog\Traits\LogsActivity;


class TokenModel extends BaseModel
{
    use HasFactory;
    
    protected $table = 'journey_api_token';
    protected $primaryKey = 'journey_api_token_id';
    protected $guarded = [];
    protected $fillable = [
        'token',
        'lob_id',
        'xutm',
        'seller_id',
        'seller_type',
        'encrypted_additional_data',
        'encrypted_form_data',
        'business_type',
        'business_code',
        'session_id',
        'decrypted_form_data'
    ];

    protected $logAttributes = [
        'token',
        'seller_id',
        'seller_type',
        'encrypted_additional_data',
        'encrypted_form_data',
        'business_type',
        'business_code'
    ];
}
