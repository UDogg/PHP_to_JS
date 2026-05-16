<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SessionTime extends BaseModel
{
    use HasFactory;
    protected $table = 'session_times';
    protected $primaryKey = 'session_id';
    protected $guarded = ['session_id'];
    protected $fillable = [
        'session_time',
        'session_content',
        'broker_name',
    ];
    protected $logAttributes = [
        'session_time',
        'session_content',
        'broker_name',
    ];
}
