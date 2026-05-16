<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class BranchMaster extends Model
{
    protected $table = 'branch_master';

    protected $fillable = [
        'branch_name'
    ];
}
