<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class KeyUtility extends BaseModel
{
    use HasFactory;
    protected  $table = "key_utility";
    protected  $fillable = ['key'];
    protected  $logAttributes = ['key'];
}
