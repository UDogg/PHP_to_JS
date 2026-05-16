<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class AUHierarchyDump extends Model
{
    protected $table = 'au_hierarchy_dump';
    protected $fillable = [
        'id',
        'designation',
        'job_id',
        'job_family',
        'department_name',	
        'department_code',
        'vertical_name',
        'vertical_code',
        'bu',
        'branch_category_id',
        'misid',
        'role_id',
        'report_role_type'
    ];
}
