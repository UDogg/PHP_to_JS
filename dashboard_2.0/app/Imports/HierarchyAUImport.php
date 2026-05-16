<?php

namespace App\Imports;

use App\Models\AuHierarchyDump;
use Maatwebsite\Excel\Concerns\ToModel;
use Maatwebsite\Excel\Concerns\WithHeadingRow;

class HierarchyAUImport implements ToModel, WithHeadingRow
{
    public function model(array $row)
    {
        $row = array_change_key_case(array_map('trim', $row), CASE_LOWER);

        if (empty($row['designation'])) {
            return null;
        }

        return new AuHierarchyDump([
            'id' => $row['id'] ?? null,
            'designation' => $row['designation'] ?? null,
            'job_id' => $row['job_id'] ?? null,
            'job_family' => $row['job_family'] ?? null,
            'department_name' => $row['department_name'] ?? null,
            'department_code' => $row['department_code'] ?? null,
            'vertical_name' => $row['vertical_name'] ?? null,
            'vertical_code' => $row['vertical_code'] ?? null,
            'bu' => $row['bu'] ?? null,
            'branch_category_id' => $row['branch_category_id'] ?? null,
            'misid' => $row['misid'] ?? null,
            'role_id' => $row['role_id'] ?? null,
            'report_role_type' => $row['report_role_type'] ?? null,
        ]);
    }
}
