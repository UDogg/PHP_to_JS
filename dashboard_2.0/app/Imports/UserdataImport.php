<?php

namespace App\Imports;

use App\Models\lobMaster;
use App\Models\SellNow;
use Illuminate\Support\Facades\DB;
use Maatwebsite\Excel\Concerns\Importable;
use Maatwebsite\Excel\Concerns\RegistersEventListeners;
use Maatwebsite\Excel\Concerns\SkipsFailures;
use Maatwebsite\Excel\Concerns\SkipsOnFailure;
use Maatwebsite\Excel\Concerns\WithEvents;
use Maatwebsite\Excel\Concerns\WithValidation;
use Maatwebsite\Excel\Concerns\ToModel;
use Maatwebsite\Excel\Validators\Failure;
use App\Models\User;
use Maatwebsite\Excel\Concerns\WithChunkReading;
use Maatwebsite\Excel\Concerns\WithHeadingRow;
use Spatie\Permission\Models\Role;

class UserdataImport implements ToModel,WithHeadingRow, WithChunkReading, WithValidation, SkipsOnFailure, WithEvents
{
    use Importable,SkipsFailures,RegistersEventListeners;
    private $request;
    protected $errors = [];
    public $Datafailures = [];
    protected $myFailures = [];
    protected  $importedData = [];

    private $userTypeList;
    private $zoneList;
    private $QualificationList;
    private $AllUserData;


    public function __construct($request, $userTypeList, $zoneList, $QualificationList, $allUserData)
    {
        $this->request = $request;
        $this->userTypeList = $userTypeList;
        $this->zoneList = $zoneList;
        $this->QualificationList = $QualificationList;
        $this->AllUserData = $allUserData;
    }
    public function excel_date_create($date) {

        if($date) {

            $excel_date = (int)$date;
            $unix_date = ($excel_date - 25569) * 86400;
            $excel_date = 25569 + ($unix_date / 86400);
            $unix_date = ($excel_date - 25569) * 86400;

            return gmdate('d/m/Y', $unix_date);
        } else{
            return $date;
        }
    }
    public function formatGender($gender)
    {
        if (strtolower($gender) == 'male') {
            return 'M';
        } elseif (strtolower($gender) == 'female') {
            return 'F';
        }
        return $gender; 
    }
    public function model(array $row)
    {
        if (isset($row['dob'])) {
            $row['dob'] = $this->excel_date_create($row['dob']);
        }
        if($this->request->type == 'P'){
            if (isset($row['license_start_date'])) {
                $row['license_start_date'] = $this->excel_date_create($row['license_start_date']);
            }
            if (isset($row['license_end_date'])) {
                $row['license_end_date'] = $this->excel_date_create($row['license_end_date']);
            }
        }
        
        if(!empty($row['gender'])){
            $row['gender'] = $this->formatGender($row['gender']) ?? null;
        }
        

        unset($row['errors']);
        foreach($this->userTypeList as $value)
        {
            if($value['Identifier'] == $this->request->type)
            {
                $usertype = $value['id'];
                break;
            }
        }
        $zoneId = null;
        foreach ($this->zoneList as $value)
        {
            if(strtoupper($value['office_zone']) == strtoupper($row['zone']))
            {
                $zoneId = $value['id'];
                break;
            }
        }
        foreach ($this->QualificationList as $value)
        {
            if($value['qualification_name'] == $row['qualification'])
            {
                $qualification_id = $value['qualification_master_id'];
                break;
            }
        }
            if(empty($qualification_id)){
                $qualification_id = null;
            }
     

        $req = $this->request;
        $errors = [];

        // Prepare fast lookup arrays for duplicates
        $emailMap     = array_column($this->AllUserData, null, 'email');
        $mobileMap    = array_column($this->AllUserData, null, 'mobile');
        $aadhaarMap   = array_column(array_filter($this->AllUserData, fn($v) => !empty($v['adhar_no'])), null, 'adhar_no');
        $panMap       = array_column(array_filter($this->AllUserData, fn($v) => !empty($v['pan_no'])), null, 'pan_no');
        $mobileToId   = array_column($this->AllUserData, 'id', 'mobile');

        // Validate current row
        if (isset($emailMap[$row['email_address']])) {
            $errors['UserEmailError'] = "This Email already exists: " . $row['email_address'];
        }
        if (isset($mobileMap[$row['mobile_number']])) {
            $errors['UserMobileError'] = "This Mobile number already exists: " . $row['mobile_number'];
        }
        if (!empty($row['aadhar_no']) && isset($aadhaarMap[$row['aadhar_no']])) {
            $errors['UserAadharError'] = "This Aadhar number already exists: " . $row['aadhar_no'];
        }
        if (!empty($row['pancard_no']) && isset($panMap[$row['pancard_no']])) {
            $errors['UserPanError'] = "This PAN card number already exists: " . $row['pancard_no'];
        }

        // Reporting User Validation
        $reportingto = null;
        $employeeCodeOverride = null;
        $empCode = null;
        if (!empty($row['reporting_mobile_no'])) {
            if (!isset($mobileToId[$row['reporting_mobile_no']])) {
                $errors['ReportingError'] = "Reporting mobile number not found: " . $row['reporting_mobile_no'];
            } else {
                $reportingto = $mobileToId[$row['reporting_mobile_no']];
                $reportingUser = User::find($reportingto);
                $empCode = $reportingUser ? credential_decrypt($reportingUser->employee_code) : null;
                // If type differs, store that employee code
                if ($reportingUser && $reportingUser->usertype != $usertype) {
                    $employeeCodeOverride = $empCode;
                    $adminUser = User::where('usertype', $usertype)->where('is_admin', 'Y')->first();
                    if ($adminUser) {
                        $reportingto = $adminUser->id;
                    }
                }
            }
        }

          // Assign Role
                $roleExists = Role::where('name', $row['role'])->exists();
                if (!$roleExists) {
                    $this->errors[] = [
                        'errors' => "This Role does not exist: " . $row['role'],
                        'row'    => $row
                    ];
                    return null;
                }
        if (!empty($errors)) {
            $this->errors[] = [
                'row' => $row,
                'errors' => $errors
            ];
            return null;
        }

        $this->importedData[] = $row;

        if (!empty($row['first_name']) && empty($this->errors)) {

            return DB::transaction(function () use ($row, $usertype, $zoneId, $req, $qualification_id, $reportingto,$employeeCodeOverride,$empCode) {

                $user = User::create([
                    'username'             => credential_encrypt($row['mobile_number']),
                    'name'                 => credential_encrypt($row['first_name']),
                    'middle_name'          => credential_encrypt($row['middle_name'] ?? ''),
                    'last_name'            => credential_encrypt($row['last_name'] ?? ''),
                    'gender'               => $row['gender'] ?? null,
                    'dob'                  => credential_encrypt($row['dob'] ?? ''),
                    'address'              => credential_encrypt($row['address'] ?? ''),
                    'pincode'              => credential_encrypt($row['pincode'] ?? ''),
                    'mobile'               => credential_encrypt($row['mobile_number']),
                    'email'                => credential_encrypt($row['email_address']),
                    'qualification'        => $qualification_id ?? null,
                    'employee_code'        => $employeeCodeOverride ?? ($row['employee_code'] ?? null),
                    'pos_code'             => $row['pos_code'] ?? null,
                    'adhar_no'             => credential_encrypt($row['aadhar_no']),
                    'pan_no'               => credential_encrypt($row['pancard_no']),
                    'license_start_date'   => $row['license_start_date'] ?? null,
                    'license_end_date'     => $row['license_end_date'] ?? null,
                    'account_holder_name'  => credential_encrypt($row['bank_account_holder_name']),
                    'account_no'           => credential_encrypt($row['bank_account_number']),
                    'ifsc_code'            => credential_encrypt($row['bank_ifsc_code']),
                    'bank_name'            => credential_encrypt($row['bank_name']),
                    'bank_city'            => credential_encrypt($row['bank_city_name']),
                    'bank_branch'          => credential_encrypt($row['branch_name']),
                    'zone_id'              => $zoneId,
                    'password'             => !empty($row['password']) ? bcrypt($row['password']) : bcrypt('Admin@123'),
                    'usertype'             => $usertype,
                    'reportingto'          => $reportingto,
                ]);

                // Assign Role
                $roleExists = Role::where('name', $row['role'])->exists();
                if ($roleExists) {
                    $user->assignRole($row['role']);
                } else {
                    $this->errors[] = [
                        'errors' => "This Role does not exist: " . $row['role'],
                        'row'    => $row
                    ];
                    return null;
                }

                // LOB Mapping
                if (strtolower($row['lob']) === 'all') {
                    $lobIds = lobMaster::where('is_enabled', 'Y')->pluck('id');
                } else {
                    $lobList = array_map('trim', explode(',', $row['lob']));
                    $lobIds = lobMaster::whereIn('lob', $lobList)->pluck('id');
                }

                foreach ($lobIds as $lobId) {
                    SellNow::insert([
                        'user_id'    => $user->id,
                        'lob_id'     => $lobId,
                        'created_at' => now(),
                    ]);
                }

                if ($user instanceof User) {
                    return $user;
                }
                return null;
            });
        }


    }

    public function chunkSize(): int
    {
        return 1000;  // Adjust this as needed
    }
    public function rules(): array
    {
        $rules = [];
        if($this->request->type == 'E')
        {
            $rules = [
                '*.email_address' => 'required|email', // Example validation rule
                '*.mobile_number' => 'required|integer|digits:10',
                '*.employee_code' => 'required',
                '*.aadhar_no'  => 'nullable|digits:12',
                '*.pancard_no' => 'nullable|regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/',
            ];
        }
        elseif($this->request->type == 'P')
        {
            $rules = [
                '*.email_address' => 'required|email', // Example validation rule
                '*.mobile_number' => 'required|integer|digits:10',
                '*.license_start_date' => 'required',
                '*.license_end_date' => 'required',
                '*.pos_code' => 'required',
                // '*.address' => 'required',
                '*.aadhar_no'  => 'required|digits:12',
                '*.pancard_no' => 'required|regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/'
            ];
        }
        elseif($this->request->type == 'Partner')
        {
            $rules = [
                '*.email_address' => 'required|email', // Example validation rule
                '*.mobile_number' => 'required|integer|digits:10',
                // '*.address' => 'required',
                // '*.aadhar_no'  => 'required|digits:12',
                // '*.pancard_no' => 'required|regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/',
            ];
        }
        $otherRules = [
          '*.lob' => 'required|string|max:30',
            '*.zone' => 'required|string|max:30',
            '*.role' => 'required|max:30',
            '*.reporting_role' => 'required|max:75',
            '*.reporting_mobile_no' => 'required|max:75',
            // '*.dob' => 'required',

        ];
        $rules = array_merge($rules, $otherRules);

        return $rules;
    }
    public function onFailure(Failure ...$Datafailures)
    {
        $this->myFailures = [];
        foreach ($Datafailures as $errkey => $errordata)
        {
            $rowIndex = $errordata->row();

            if (isset($this->myFailures[$rowIndex])) {
                $this->myFailures[$rowIndex]['errors'][] = $errordata->errors()[0];
            } else {
            $this->importedData[] = $errordata->values();
                $this->myFailures[$rowIndex] = [
                    'errors' =>
                        [$errordata->errors()[0]],

                    'row' => $errordata->values(),
                ];
            }
        }
        $this->errors = array_merge($this->errors,$this->myFailures);
    }
    // Optional: Log or process the failures as needed
    public function getErrors()
    {
        DB::rollBack();
      return  $this->errors;
    }

    public function getImportedData()
    {
        return $this->importedData;
    }


}

