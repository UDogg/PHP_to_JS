<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class AccidentCategory extends Model
{
    protected $table = "accidents";
    protected $fillable = ['nature_of_accident', 'status'];
}
