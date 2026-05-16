<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class StagemasterModel extends BaseModel
{
    use HasFactory;
    protected $table = 'stage_master';
    protected $fillable = ['id','sub_stage_name','stage_name','priority'];
    protected $logAttributes = ['id','sub_stage_name','stage_name','priority'];
}
