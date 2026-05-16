<?php

namespace App\Imports;

use App\Models\AuBranch;
use Maatwebsite\Excel\Concerns\ToModel;
use Maatwebsite\Excel\Concerns\WithHeadingRow;
use Maatwebsite\Excel\Concerns\WithChunkReading;

class AUBranchImport implements ToModel, WithHeadingRow, WithChunkReading
{
    public function model(array $row)
    {
        if (empty($row['branchname'])) {
            return null;
        }

        return new AuBranch([
            'BranchID' => $row['branchid'] ?? null,
            'BranchCode' => $row['branchcode'] ?? null,
            'BranchName' => $row['branchname'] ?? null,
            'Circle' => $row['circle'] ?? null,
            'Zone' => $row['zone'] ?? null,
            'Region' => $row['region'] ?? null,
            'Cluster' => $row['cluster'] ?? null,
            'State' => $row['state'] ?? null,
            'State_Wheels' => $row['state_wheels'] ?? null,
            'Hub_Wheels' => $row['hub_wheels'] ?? null,
            'State_Agri_SME' => $row['state_agri_sme'] ?? null,
            'Hub_Agri_SME' => $row['hub_agri_sme'] ?? null,
            'State_Home_Loans' => $row['state_home_loans'] ?? null,
            'Hub_Home_Loans' => $row['hub_home_loans'] ?? null,
            'State_SBL_MSME' => $row['state_sbl_msme'] ?? null,
            'Hub_SBL_MSME' => $row['hub_sbl_msme'] ?? null,
            'City' => $row['city'] ?? null,
            'Pincode' => $row['pincode'] ?? null,
            'Category_Urban_Core' => $row['category_urban_core'] ?? null,
            'RBI_Classification' => $row['rbi_classification'] ?? null,
            'Branch_Category3' => $row['branch_category3'] ?? null,
            'Branch_Launch_Date' => $row['branch_launch_date'] ?? null,
            'Branch_Type' => $row['branch_type'] ?? null,
            'Tier' => $row['tier'] ?? null,
            'Branch_Address' => $row['branch_address'] ?? null,
            'Reporting_Branch_Code' => $row['reporting_branch_code'] ?? null,
            'Status' => $row['status'] ?? null,
        ]);
    }

    public function chunkSize(): int
    {
        return 500;
    }
}
