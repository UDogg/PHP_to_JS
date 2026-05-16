<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SectionField extends BaseModel
{
    use HasFactory;
    protected $primaryKey = 'field_id';
    protected  $table = 'section_fields';
    protected  $fillable = [
        'lob','service_support_type','section_name','section_field_name'

    ];
    protected  $logAttributes = [
        'lob','service_support_type','section_name','section_field_name'

    ];
}
