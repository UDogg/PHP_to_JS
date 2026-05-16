<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;


class stateMaster extends Model
{
    use HasFactory, SoftDeletes;

    protected $table = 'state_masters';
    protected $primaryKey = 'state_id';

    protected $fillable = [
        'state_name',
        'state_code',

    ];
}
