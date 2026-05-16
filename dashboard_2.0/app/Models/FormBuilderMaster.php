<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class FormBuilderMaster extends BaseModel
{
    use HasFactory;

    protected $table = 'form_builder_masters';

    protected $guarded = ['id'];
    
    
}
