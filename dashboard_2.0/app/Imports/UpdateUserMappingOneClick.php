<?php

namespace App\Imports;

use App\Models\User;
use Maatwebsite\Excel\Concerns\ToModel;

class UpdateUserMappingOneClick implements ToModel
{
    /**
    * @param array $row
    *
    * @return \Illuminate\Database\Eloquent\Model|null
    */
    public function model(array $row)
    {
        $userData = User::where('mobile', credential_encrypt($row[0]))->first();
        $userDataReporting = User::where('mobile', credential_encrypt($row[1]))->first();
        if($userData && $userDataReporting){
            User::where('mobile', credential_encrypt($row[0]))
            ->update(['reportingto'=>$userDataReporting->id,'employee_code'=>$userDataReporting->employee_code]);
        
            $userData = User::where('mobile', credential_encrypt($row[0]))->first();
        }
        return $userData;

    }
}
