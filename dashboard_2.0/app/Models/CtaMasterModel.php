<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class CtaMasterModel extends BaseModel
{
    use HasFactory;
    protected  $table = "cta_master";

    protected $fillable = [
        'stage',
        'cta_name',
        'lob',
    ];

}
