<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class CustomerPolicyExpire extends Model
{
    // Set custom table name
    protected $table = 'customer_policy_expire';

    // Mass assignable fields
    protected $fillable = [
        'customer_id',
        'lob_id',
        'policy_no',
        'policy_end_date',
        'mobile_no'
    ];
}
