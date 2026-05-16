<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class EmailType extends BaseModel
{
    use HasFactory;
    protected $primaryKey = 'type_id';
}
