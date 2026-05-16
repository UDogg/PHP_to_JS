<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use MongoDB\Laravel\Eloquent\SoftDeletes;

class TagName extends Model
{
    use HasFactory,SoftDeletes;
    protected  $table = 'tag_names';
    protected  $primaryKey = 'tag_id';
    protected  $fillable = [

        'tag_name',

    ];
}
