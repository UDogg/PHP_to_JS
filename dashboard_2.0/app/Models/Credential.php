<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\Artisan;

class Credential extends BaseModel
{
    use HasFactory;
    protected $table = 'config_settings';
    protected $primaryKey = 'credential_id';
    protected $guarded = ['credential_id'];
    protected $fillable = [
        'credential_label',
        'credential_key',
        'credential_value',
        'enviroment',
        'encryption_method',
        'configuration'
    ];

    protected $logAttributes = [
        'credential_label',
        'credential_key',
        'credential_value',
        'enviroment',
        'encryption_method',
        'configuration'
    ];
    protected static function boot()
    {
        parent::boot();
        static::updated(function ($model) {
          Artisan::call('optimize:clear');
        });
    }
}
