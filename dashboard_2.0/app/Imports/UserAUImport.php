<?php

namespace App\Imports;

use App\Models\AuBranch;
use App\Models\AUHierarchyDump;
use App\Models\lobMaster;
use App\Models\SellNow;
use App\Models\User;
use App\Models\UserAdditionalData;
use Carbon\Carbon;
use Illuminate\Support\Collection;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;

use Maatwebsite\Excel\Concerns\{
    ToCollection,
    WithChunkReading,
    WithHeadingRow
};

class UserAUImport implements ToCollection, WithChunkReading, WithHeadingRow
{    
    protected $request;

    protected $auth;

    protected $authenticatedUser;

    protected $userRoleMapping;

    protected $UserlobMapping;

    protected $rolecontroller;

    protected $sellNowController;
    protected $admins;
    protected $branches;
    protected $roles;
    protected $lobIds;

    // Constructor accepts request data
    public function __construct($request, $auth, $rolecontroller, $sellNowController)
    {
        $this->request = $request;
        $this->authenticatedUser = $auth;
        $this->userRoleMapping = $rolecontroller;
        $this->UserlobMapping = $sellNowController;
        $this->lobIds = lobMaster::where('is_enabled', 'Y')->pluck('id');
        $this->admins = User::where('is_admin','Y')->get()->groupBy('usertype');
        $this->branches = DB::table('au_branch_dump')->pluck('BranchID','BranchCode');
        $this->roles = AUHierarchyDump::pluck('role_id','designation',);

    }
    public function chunkSize(): int
    {
        return 1000;
    }


    public function collection(Collection $rows)
    {
        DB::beginTransaction();


        foreach ($rows as $row) {

            if($row['emailid'] =='' || $row['emailid'] == null){
                continue; // Skip rows with empty email
            }
            if($row['mobileno'] =='' || $row['mobileno'] == null){
                continue; // Skip rows with empty email
            }

            $login = trim($row['userloginid']);

            $reportingEmployeeCode = filter_var($login, FILTER_VALIDATE_EMAIL) ? null : $login; 

            $qrCode_generated = generateQrcode();
            $secret = $qrCode_generated['secret'];
            $totp_secret = credential_encrypt($secret);

            // ===== USER TYPE =====
            $userType = ($row['sp_codes'] != 'NOT_FOUND' ? 7 : 1);

            // ===== REPORTING =====
            $admin = $this->admins[$userType][0] ?? null;
            $reportingTo = $admin?->id;

            // ===== NAME CLEAN =====
            $name = preg_replace('/\b(mr|mrs|ms|miss|dr)\.?\s*/i', '', $row['username']);
            $name = ucwords(strtolower(trim($name)));
            $parts = explode(' ', $name);

            $first = $parts[0] ?? '';
            $last = count($parts) > 1 ? array_pop($parts) : '';
            $middle = implode(' ', array_slice($parts,1));

            preg_match('/\b\d{6}\b/', $row['address'] ?? '', $pin);

            if($reportingEmployeeCode && $row['reportingto']!='0' && $row['reportingto']!=''){
                $reportingToData = User::where('username', credential_encrypt($row['reportingto']))->first();
                if(! $reportingToData){                
                    $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                }
                // if ($row->Sellertype == 'P') {
                //     if ($reportingToData->usertype == 3) {
                //         $reportingTo = $reportingToData->id;
                //     } else {
                //         $reportingEmployeeCode = $row['reportingto'];
                //         $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                //     }
                // } else {
                    if ($reportingToData) {
                        $reportingTo = $reportingToData->id;
                    } else {
                        $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
                    }
                // }
            }else{
                $reportingTo = User::where('usertype', $userType)->where('is_admin', 'Y')->pluck('id')->first();
            }

            $fullName = trim($first . ' ' . $middle . ' ' . $last);

            $inserted = User::updateOrCreate(
                ['username' => credential_encrypt($row['userloginid'])], 
                ['name' => credential_encrypt($first),
                'middle_name' => credential_encrypt($middle),
                'last_name' => credential_encrypt($last),
                'email' => credential_encrypt($row['emailid']),
                'mobile' => credential_encrypt($row['mobileno']),
                'address' => credential_encrypt($row['address']),
                'pincode' => credential_encrypt($pin[0] ?? null),
                'password' => Hash::make('Admin@123'),
                'totp_secret' => $totp_secret,
                'employee_code' => $reportingEmployeeCode,
                'usertype' => $userType,
                'reportingto' => $reportingTo,
                'pan_no' => credential_encrypt($row['panno']),
                'dob' => $row['emp_dob'] ? credential_encrypt($row['emp_dob']) : null,
                'zone_id' => 1,
                'status' => 'Y',
                'user_code' => $row['userloginid'],
            ]);

            $user_id = $inserted->id;

            $user_role_id = AUHierarchyDump::where('department_code', $row['departmentcode'])
                            ->where('vertical_code', $row['verticalid'])
                            ->where(function ($q) use ($row) {
                                $q->where('job_id', $row['jobid'])
                                ->orWhereNull('job_id');
                            })
                            ->orderByRaw('job_id IS NULL')   // exact match first
                            ->value('role_id');

            $user_role_id = $row['sp_codes'] != 'NOT_FOUND' ? 12 : ($user_role_id !="" ? $user_role_id : 24);
                            

            $inserted = UserAdditionalData::updateOrCreate(
            ['user_id' => $user_id,],[
                'job_id' => $row['jobid'],
                'role_id' => $user_role_id,
                'RBM' => $row['rbm'],
                'CBM' => $row['cbm'],
                'department_code' => $row['departmentcode'],
                'vertical_code' => $row['verticalid'],
                'functional_role' => $row['functionalrole'],
                'user_salary' => null,
                'is_sp' => $row['sp_codes'] != 'NOT_FOUND' ? 'Y' : 'N',
                'sp_name' => $fullName,
                'sp_code' => $row['sp_codes']!= 'NOT_FOUND' ? $row['sp_codes'] : null,
                'sp_type' => $row['insurance_type'] != 'NOT_FOUND' ? $row['insurance_type'] : null,
                'certificate_valid_from' => $row['valid_from'] != 'NOT_FOUND' ? $this->safeDate($row['valid_from']) : null,
                'certificate_valid_till' => $row['valid_till'] != 'NOT_FOUND' ? $this->safeDate($row['valid_from']) : null,
            ]);

            $branch_id = DB::table('au_branch_dump')->where('BranchCode', $row['branchcode'])->pluck('BranchID');

            foreach ($branch_id as $branch_value) {
                DB::table('user_branch_relation')
                    ->where('user_id', $user_id)->where('branch_id', $branch_value)
                    ->delete();

                $inserted = DB::table('user_branch_relation')->insert([
                    'user_id' => $user_id,
                    'branch_id' => $branch_value,
                ]);
            }

            $this->request->merge(['user_id' => $user_id, 'role_id' => $user_role_id]);

            $userrolemapping = $this->userRoleMapping->UserRoleMapping($this->request);

            SellNow::where('user_id', $user_id)->delete();

            foreach ($this->lobIds as $value) {

                $userlobMapping = SellNow::create([
                    'user_id' => $user_id,
                    'lob_id' => $value,
                    'created_at' => Carbon::now(),
                    'updated_at' => null,
                ]);
            }

            DB::commit();

        }
    }

    function safeDate($value)
    {
        if ($value === null) {
            return null;
        }

        $value = trim((string) $value);

        if ($value === '' || strtolower($value) === 'null') {
            return null;
        }

        // Excel numeric date
        if (is_numeric($value)) {
            return Carbon::instance(
                ExcelDate::excelToDateTimeObject($value)
            );
        }

        // Format: 22 March 2023
        if (preg_match('/^\d{1,2}\s+[A-Za-z]+\s+\d{4}$/', $value)) {
            try {
                return Carbon::createFromFormat('d F Y', $value);
            } catch (\Exception $e) {
                return null;
            }
        }

        // Last fallback — let Carbon try
        try {
            return Carbon::parse($value);
        } catch (\Exception $e) {
            return null;
        }
    }
}
