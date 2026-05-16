<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class Menu extends BaseModel
{
    use HasFactory;
    protected $table = 'menu';
    protected $primaryKey = 'menu_id';
    protected $guarded = ['menu_id'];
    protected $fillable = [
        'menu_name',
        'menu_link',
        'menu_slug',
    ];

    protected $logAttributes = [
        'menu_name',
        'menu_link',
        'menu_slug',
    ];
}
