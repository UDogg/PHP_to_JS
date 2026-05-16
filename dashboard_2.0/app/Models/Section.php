<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class Section extends BaseModel
{
    use HasFactory;
    protected $primaryKey = 'section_id';
    protected  $table = 'sections';
    protected  $fillable = [
        'lob','service_support_type','section_name',

    ];
    protected  $logAttributes = [
        'lob','service_support_type','section_name',

    ];
}
