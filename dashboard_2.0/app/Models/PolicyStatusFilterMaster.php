<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class PolicyStatusFilterMaster extends BaseModel
{
    use HasFactory;
    protected $table = 'policy_status_filter_master';
    protected $fillable = [
        'filtername',
        'type',
        'key',
        'value',
        'lob',
        'column'
    ];
    protected $logAttributes = [
        'filtername',
        'type',
        'key',
        'value',
        'lob',
        'column'
    ];
}
