<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class keyUtilityMapping extends BaseModel
{
    use HasFactory;
    protected  $table = "key_utility_mapping";
    protected  $fillable = ['mapping_id','lob','key_id'];
    protected  $logAttributes = ['mapping_id','lob','key_id'];
}
