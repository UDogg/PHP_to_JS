<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class StatusMaster extends BaseModel
{
    use HasFactory;
    protected $primaryKey = 'status_id';
    protected  $table = 'status_masters';
    protected  $fillable = [
        'status_name',

    ];
    protected  $logAttributes = [
        'status_name',

    ];
}
