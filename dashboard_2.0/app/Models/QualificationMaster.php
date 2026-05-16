<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class QualificationMaster extends Model
{
    use HasFactory;

    protected $guarded = [];

    protected $table = 'qualification_master';
    protected $primaryKey = 'qualification_master_id';
    protected $fillable = [
        'qualification_name',
    ];
    protected  $logAttributes = [
        'qualification_name',
    ];

}
