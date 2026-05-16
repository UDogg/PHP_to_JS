<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class Event extends BaseModel
{
    use HasFactory;
    protected $table = 'event';
    protected $primaryKey = 'event_id';
    protected $fillable = ['event_name',];

    protected $logAttributes = ['event_name',];
}
