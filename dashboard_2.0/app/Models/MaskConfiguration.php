<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class MaskConfiguration extends BaseModel
{
    use HasFactory;
    use SoftDeletes;
    protected  $table = "mask_configuration";
    protected  $fillable = ['key_name','masking_position','masking_symbol','for_report','status'];
    protected $logAttributes = ['key_name','masking_position','masking_symbol','for_report','status'];
}
