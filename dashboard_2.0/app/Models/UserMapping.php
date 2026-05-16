<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Laravel\Sanctum\HasApiTokens;

class UserMapping extends Model
{
    use HasFactory,HasApiTokens;
 protected $table = "user_mappings";
    protected $fillable = [
        'user_id',
        'user_type',
        'status',
        'role_id',
        'reportingto',
        'employee_code',
        'reportingtoemployee'
    ];
    public function user()
    {
        return $this->belongsTo(User::class, 'user_id');
    }

    public function role()
    {
        return $this->belongsTo(Role::class, 'role_id');
    }

    public function reportingToUser()
    {
        return $this->belongsTo(User::class, 'reportingto');
    }
}
