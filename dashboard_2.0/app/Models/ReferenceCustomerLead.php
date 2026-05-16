<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class ReferenceCustomerLead extends Model
{
    protected $table = 'reference_customer_lead';
    protected $fillable = [
        'name',
        'mobile',
        'email',
        'created_by'
    ];
}
