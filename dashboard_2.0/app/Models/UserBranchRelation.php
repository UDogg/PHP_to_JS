<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class UserBranchRelation extends Model
{
    protected $table = "user_branch_relation";
    protected $fillable = [
        'user_id',
        'branch_id',
        'status'
    ];

    public function branch()
    {
        return $this->belongsTo(AuBranch::class, 'branch_id', 'BranchID');
    }    
}
