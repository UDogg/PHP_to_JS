<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class ConfigMaster extends BaseModel
{
    use HasFactory;
    protected  $table = 'ConfigMaster';
    protected  $fillable = ['key'];
    protected  $logAttributes = ['key'];
}
