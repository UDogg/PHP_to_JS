<?php

namespace App\Services;

use App\Models\EmployeePayrollId;
use App\Models\User;
use Illuminate\Support\Facades\DB;
use Carbon\Carbon;

class OracleAgentMasterNonPayrollService
{
      public function processAgentMasterData()
    {
        $oracle = DB::connection('oracle');


        $employeeParentMap = [];
        $existingUsernames = [];

        User::select('id', 'username')
            ->chunk(1000, function ($users) use (&$employeeParentMap, &$existingUsernames) {
                foreach ($users as $user) {
                    $username = credential_decrypt($user->username);

                    $employeeParentMap[$username] = $user->id;
                    $existingUsernames[$username] = true; 
                }
            });

        $oracleRows = $oracle->select("
                   SELECT ANA_RM_ID,
                   EXIST_CODE,
                   AGENT_NAME,
                   MOBILE,
                   EMAIL,
                   AGENT_CODE,
                   PART_PAYROLL_ID
                   FROM WEALTHMAKER.VW_PRT_AGENT_MASTER
                ");

        $insertCount = 0;

        DB::beginTransaction();

        try {

            $batch = [];

            foreach ($oracleRows as $row) {

                $row = (array) $row;

                if (empty($row['EXIST_CODE'])) {
                    continue;
                }

                if (isset($existingUsernames[$row['EXIST_CODE']])) {
                    continue;
                }

                $batch[] = [
                    'employee_name'  => $row['AGENT_NAME'],
                    'user_name'      => $row['EXIST_CODE'],
                    'mobile'         => $row['MOBILE'],
                    'email'          => $row['EMAIL'],
                    'parent'         => $employeeParentMap[$row['ANA_RM_ID']] ?? 1,
                    'employee_code'  => $row['AGENT_CODE'],
                    'employee_type'  => !empty($row['PART_PAYROLL_ID']) ? 'PTE' : null,
                    'ANA_RM_ID'      => $row['ANA_RM_ID'],
                ];

                if (count($batch) === 500) {
                    EmployeePayrollId::insert($batch);
                    $insertCount += count($batch);
                    $batch = [];
                }
            }

            if (!empty($batch)) {
                EmployeePayrollId::insert($batch);
                $insertCount += count($batch);
            }

            DB::commit();

            return [
                'status'          => true,
                'inserted_count'  => $insertCount,
                'message'         => 'Agent master sync completed successfully'
            ];

        } catch (\Exception $e) {

            DB::rollBack();

            return [
                'status'  => false,
                'message' => $e->getMessage()
            ];
        }
    }

}
