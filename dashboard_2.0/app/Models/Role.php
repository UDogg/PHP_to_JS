<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class Role extends Model
{
    protected $table = 'roles'; // Ensure this matches your table name

    // Define a relationship to get the parent role
    public function parent()
    {
        return $this->belongsTo(Role::class, 'reporting_role');
    }

    // Define a relationship to get child roles
    // public function children()
    // {
    //     return $this->hasMany(Role::class, 'reporting_role');
    // }

    public function children($userType )
    {
    return $this->hasMany(Role::class, 'reporting_role')->when($userType, function ($query) use ($userType) {
        $query->where('user_type', $userType);
    });
    }
}

