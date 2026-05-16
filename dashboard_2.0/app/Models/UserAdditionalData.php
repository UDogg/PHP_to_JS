<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class UserAdditionalData extends Model
{
    protected $fillable = [
        'user_id',
        'job_id',
        'branch_code',
        'date_of_joining',
        'date_of_leaving',
        'role_id',
        'L1_user_mobile',
        'L1_user_email',
        'L1_user_id',
        'L2_user_id',
        'L3_user_id',
        'department_code',
        'vertical_code',
        'functional_role',
        'user_salary',
        'is_sp',
        'sp_name',
        'sp_code',
        'sp_type',
        'noc_issued',
        'sp_certificate_date',
        'certificate_valid_from',
        'certificate_valid_till',
    ];
}
