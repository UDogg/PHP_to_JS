<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class LogsApi extends Model
{
    protected $table = 'logs_api_table';
    protected $fillable = [
        'url',
        'method',
        'headers',
        'request',
        'response',
        'status_code',
        'api_type'
    ];
}
