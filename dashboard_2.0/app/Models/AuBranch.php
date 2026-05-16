<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class AuBranch extends Model
{
    //
    protected $table = "au_branch_dump";

    protected $fillable = [
        'BranchID',
        'BranchCode',
        'BranchName',
        'Circle',
        'Zone',
        'Region',
        'Cluster',
        'State',
        'State_Wheels',
        'Hub_Wheels',
        'State_Agri_SME',
        'Hub_Agri_SME',
        'State_Home_Loans',
        'Hub_Home_Loans',
        'State_SBL_MSME',
        'Hub_SBL_MSME',
        'City',	
        'Pincode',
        'Category_Urban_Core',
        'RBI_Classification',
        'Branch_Category3',
        'Branch_Launch_Date',
        'Branch_Type',
        'Tier',
        'Branch_Address',
        'Reporting_Branch_Code',
        'Status',
    ];
}
