<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class ClaimStageMaster extends Model
{
    protected $table = "claim_stage_master";
    protected $fillable = [
        'stage_name'
    ];
}
