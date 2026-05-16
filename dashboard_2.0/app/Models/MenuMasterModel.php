<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class MenuMasterModel extends BaseModel
{
    use HasFactory , SoftDeletes;
    protected $table = 'MenuMaster';
    protected  $fillable = [
        'menu',
        'route',
        'icon',
        'menuId',
        'subMenuId',
        'status',
        'front_end_url',
        'is_child',
        'isFrontEnd',
        'order_by',
        'filename'

    ];
    protected  $logAttributes = [
        'menu',
        'route',
        'icon',
        'menuId',
        'subMenuId',
        'status',
        'front_end_url',
        'order_by',
        'filename'
    ];
}
