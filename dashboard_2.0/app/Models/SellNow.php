<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SellNow extends BaseModel
{
    use HasFactory;
    protected $table = "user_lob_relation";
    protected  $fillable = [
        'lob_id','user_id'

    ];
    protected  $logAttributes = [
        'lob_id','user_id'

    ];
}
