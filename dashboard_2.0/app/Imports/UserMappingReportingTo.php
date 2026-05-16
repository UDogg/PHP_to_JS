<?php

namespace App\Imports;

use App\Models\User;
use Illuminate\Support\Facades\DB;
use Maatwebsite\Excel\Concerns\Importable;
use Maatwebsite\Excel\Concerns\SkipsFailures;
use Maatwebsite\Excel\Concerns\SkipsOnFailure;
use Maatwebsite\Excel\Concerns\ToModel;
use Maatwebsite\Excel\Concerns\WithChunkReading;
use Maatwebsite\Excel\Concerns\WithHeadingRow;
use Maatwebsite\Excel\Concerns\WithValidation;
use Maatwebsite\Excel\Validators\Failure;
use Spatie\Permission\Models\Role;

class UserMappingReportingTo implements ToModel,WithHeadingRow,WithChunkReading, SkipsOnFailure, WithValidation
{
    use Importable, SkipsFailures;
    /**
    * @param array $row
    *
    * @return \Illuminate\Database\Eloquent\Model|null
    */
    protected $Errors = [];
    protected  $Datafailures = [];
    protected  $importedData = [];
    protected $request;
    protected $rolelist;
    protected $userlist;
    private  $decptAllusersData;
    private $pospAdminRoleId ;
    public function __construct($request, $userlist)
    {
        $this->request = $request;
        $this->userlist = $userlist;
        $AllUsersData = User::select('id','username','mobile','email','employee_code')->with('roles:id,name')->get();
        $this->decptAllusersData = $AllUsersData->map(function ($user) {
            $user->username =  credential_decrypt($user->username);
            $user->mobile = credential_decrypt($user->mobile);
            $user->email = credential_decrypt($user->email);
            $user->adhar_no = credential_decrypt($user->adhar_no);
           $user->pan_no = credential_decrypt($user->pan_no);
            return $user;
        })->toArray();
        if($request->type == 'P'){
            // $this->pospAdminRoleId = User::role('Posp Admin')->first()->id;
        }
        
    }
    public function model(array $row)
    {
        $this->importedData = $row;
        $req = $this->request;
        return DB::transaction(function () use ($row,$req) {
            //        gettitng the reporting role id from role list
        $continue  = true;
        $reportingRole = $row['reporting_role'];
        $reportingUserName = $row['reporting_mobile_no'];

       $currentUserId = null;
        $currentUserName = $req->type == 'E' ? $row['mobile_number'] : 
        ($req->type == 'P' ? $row['mobile_number'] : 
        ($req->type == 'Partner' ? $row['mobile_number'] : null));
//        getting user id of that reporing role to assign to current user reportinh role
        foreach ($this->userlist as $uKey => $user)
        {
            if($user['username'] == $currentUserName)
            {
                $currentUserId = $user['id'];
                break;
            }
        }
        if($currentUserId == null)
        {
            $this->Errors[] = [
                'errors' => $currentUserName.' not found in user list',
                'row' => $row
            ] ;
            $continue = false;
        }
        $error = false;
        if($continue)
        {
            foreach($this->userlist as $user)
            {
                if($user['username'] == $reportingUserName)
                {
                    $this->AssignReportingTo($user['roles'][0]['name'],$reportingRole,$currentUserId,$row,$user['id']);
                   $error = false;
                   break;
                }
                else
                {
                    if($req->type == 'P' || $req->type == 'Partner')
                    {
                        foreach($this->decptAllusersData as $userEmployee)
                        {
                            if($userEmployee['username'] == $reportingUserName)
                            {
                                $employeeCode = $userEmployee['employee_code']; // we are taking empcode of the reporting user
                                $this->AssignReportingToEmployee($userEmployee['roles'][0]['name'],$reportingRole,$currentUserId,$row,$user,$this->pospAdminRoleId,$employeeCode,$userEmployee['id']);
                                break;
                            }
                        }
                    }
                    else
                    {
                        $error = true;
                    }

                }
            }
            if($error == true)
            {
                $this->ReportingUserNotFound($row,$currentUserId);
            }

            if(count($this->Errors) > 0)
            {
                $userdelete = User::where('id',$currentUserId)->forceDelete();
            }
        }
        });
    }
    public function GetErrors()
    {
        return $this->Errors;
    }
    public function rules(): array
    {
        $rules = [];
        if($this->request->type == 'E')
        {
            $rules = [
                '*.email_address' => 'required|email', // Example validation rule
                '*.user_name'  => 'required', // Another rule
                '*.mobile_number' => 'required|integer',
                '*.aadhar_no'  => 'required|digits:12',
                '*.pancard_no' => 'required|regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/',
            ];
        }
        elseif($this->request->type == 'P')
        {
            $rules = [
                '*.email_address' => 'required|email', // Example validation rule
                // '*.pos_user_name'  => 'required|string', // Another rule
                '*.mobile_number' => 'required|integer',
            ];
        }
        elseif($this->request->type == 'Partner')
        {
            $rules = [
                '*.email_address' => 'required|email', // Example validation rule
                // '*.partner_user_name'  => 'required', // Another rule
                '*.mobile_number' => 'required|integer|digits:10',
                // '*.address' => 'required',
                '*.aadhar_no'  => 'required|digits:12',
                '*.pancard_no' => 'required|regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/',
            ];
        }

        return $rules;
    }
    public function onFailure(Failure ...$Datafailures)
    {
        foreach ($Datafailures as $errkey => $errordata)
        {
            $this->importedData[] = $errordata->values();
            DB::rollBack();
            $this->myFailures[$errkey] = [
                'errors' =>[
                    'validationError' => $errordata->errors()[0],
                ],
                'row' => $errordata->values()
            ];
        }
        $this->Errors = array_merge($this->Errors,$this->myFailures);
    }

    public function chunkSize(): int
    {
        return 1000;  // Adjust this as needed
    }
    private function AssignReportingTo($rolename,$reportingRole,$currentUserId,$row,$userId):void
    {
        if($rolename == $reportingRole)
        {
            $userMappingUpdate = User::where('id',$currentUserId)->update(['reportingto' => $userId]);
            if(!$userMappingUpdate)
            {
                DB::rollBack();
            }
        }
        else
        {
            $this->Errors[] =[
                'errors' => 'Reporting user role not matched for this user '. $row['reporting_username'],
                'row' => $row
            ];
            $userdelete = User::where('id',$currentUserId)->forceDelete();
            DB::rollBack();

        }
    }
    private function AssignReportingToEmployee($rolename,$reportingRole,$currentUserId,$row,$userId,$PosAdminId,$employeeCode,$reportingEmployeeId):void
    {
        if($rolename == $reportingRole)
        {
            $userMappingUpdate = User::where('id',$currentUserId)->update([
                'reportingto' => $reportingEmployeeId,
                'employee_code' => $employeeCode
            ]);
            if(!$userMappingUpdate)
            {
                DB::rollBack();
            }
        }
        else
        {
            $this->Errors[] =[
                'errors' => 'Reporting user role not matched for this user '. $row['reporting_username'],
                'row' => $row
            ];
            // $userdelete = User::where('id',$currentUserId)->forceDelete();
            DB::rollBack();

        }
    }

    private function ReportingUserNotFound($row,$currentUserId)
    {
        $this->Errors[] =[
            'errors' => 'Reporting user  not found for this user '. $row['reporting_username'],
            'row' => $row
        ];
    }
}
