<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class UserAccessManagment extends BaseModel{
    use HasFactory;
    protected $table = 'user_access_managment';
    protected $primaryKey = 'id';
    protected $guarded = [];
    protected $fillable = [
       'role_id',
       'user_id',
       'type',
       'data',
       'status'
    ];

    protected $logAttributes = [
       'role_id',
       'user_id',
       'type',
       'data',
       'status'
    ];
}

