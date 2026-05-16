<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class VerticalMaster extends BaseModel
{
    use HasFactory;
    protected $table = 'vertical_masters';
    protected  $fillable = [
        'vertical_name',
        'created_by'

    ];
    protected  $logAttributes = [
        'vertical_name',
        'created_by'
    ];
}
