<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class EmployeePayrollId extends Model
{
    protected $table = 'employee_payroll_id';

    protected $fillable = [
        'employee_name',
        'user_name',
        'mobile',
        'email',
        'parent',
        'employee_code',
        'employee_type',
        'ANA_RM_ID'
    ];
}
