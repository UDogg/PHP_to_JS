<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class corporatesOnBoardingMaster extends Model
{
    use HasFactory;
    protected $table = "corporates_on_boarding_master";

    protected $fillable = [
        'id',
        'first_name',
        'last_name',
        'company_name',
        'designation',
        'work_email',
        'mobile_no',
        'no_of_employees',
        'is_verified',
        'is_verified_required_to',
        'other_email',
        'document',
        'company_domain',
        'selected_domain',
        'status'
  
    ];
}
