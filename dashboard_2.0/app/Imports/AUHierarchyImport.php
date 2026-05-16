<?php

namespace App\Imports;

use App\Models\AUHierarchyDump;
use Maatwebsite\Excel\Concerns\ToModel;

class AUHierarchyImport implements ToModel
{
    /**
    * @param array $row
    *
    * @return \Illuminate\Database\Eloquent\Model|null
    */
    public function model(array $row)
    {
        return AUHierarchyDump::updateOrCreate(
            ['id' => $row['id']],
            [
                'designation'     => $row['designation'] ?? null,
                'job_id'          => $row['jobid'] ?? null,
                'job_family'      => $row['jobfamily'] ?? null,
                'department_name' => $row['departmentname'] ?? null,
                'department_code' => $row['departmentcode'] ?? null,
                'vertical_name'   => $row['verticalname'] ?? null,
                'vertical_code'   => $row['verticalcode'] ?? null,
                'bu'              => $row['bu'] ?? null,
                'misid'           => $row['misid'] ?? null,
                'role_id'         => $row['roleid'] ?? null,
                'report_role_type'=> $row['reportroletype'] ?? null,
            ]
        );
    }
}
