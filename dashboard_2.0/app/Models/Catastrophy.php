<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class Catastrophy extends Model
{
    protected $table = 'catastrophy';
    protected $fillable = [
        'status',
        'isOngoing',
        'catastrophicDateValidUpto',
        'catastrophicDate',
        'catastrophicCode',
        'catastrophicName'
    ];
}
