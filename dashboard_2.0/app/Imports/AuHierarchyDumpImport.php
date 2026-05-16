<?php

namespace App\Imports;

use Illuminate\Support\Collection;
use Maatwebsite\Excel\Concerns\ToCollection;
use Maatwebsite\Excel\Concerns\WithHeadingRow;
use Illuminate\Support\Facades\DB;

class AuHierarchyDumpImport implements ToCollection, WithHeadingRow
{
    public function collection(Collection $rows)
    {
        $data = [];

        foreach ($rows as $row) {
            $data[] = [
                'bu'                 => $row['bu'] ?? null,
                'department_code'    => $row['department_code'] ?? null,
                'department_name'    => $row['department_name'] ?? null,
                'designation'        => $row['designation'] ?? null,
                'job_family'         => $row['job_family'] ?? null,
                'job_id'             => $row['job_id'] ?? null,
                'report_role_type'   => $row['report_role_type'] ?? null,
                'vertical_code'      => $row['vertical_code'] ?? null,
                'vertical_name'      => $row['vertical_name'] ?? null,
                'role_id'            => $row['role_id'] ?? null,
            ];
        }

        if (!empty($data)) {
            DB::table('au_hierarchy_dump')->insert($data);
        }
    }
}
