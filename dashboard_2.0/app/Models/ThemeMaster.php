<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class ThemeMaster extends Model
{
    use HasFactory;

    protected $table = 'themes';
    protected $fillable = [
        'theme_name',
        'theme_value',
        'user_id',
        'status'
    ];
    protected $casts = [
        'theme_value' => 'array', 
    ];
}
