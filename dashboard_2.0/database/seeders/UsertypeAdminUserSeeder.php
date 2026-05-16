<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Log;

class UsertypeAdminUserSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        $usertype = DB::table('usertypes')->select('id')->where('Identifier', 'E')->first();
        $employeeCode = 2222;
        $lob = DB::table('lob_master')->select('id')->whereIn('lob', ['CAR','GCV','PCV','health','travel','super top up','BIKE','MISC','term','investment'])->get();

        $lastUserId = DB::table('users')->select('id')->where('name',credential_encrypt('Employee Admin'))->first();
        $role = DB::table('roles')->select('id')->where('name', 'Employee Admin')->first();


        if(empty($lastUserId))
        {
            $usercreate = DB::table('users')->insert([
                'name' => credential_encrypt('Employee Admin'),
                'email' => credential_encrypt('employee_admin@fyntune.com'),
                'password' => Hash::make('Admin@123'),
                'username' => credential_encrypt('employee_admin'),
                'mobile' => credential_encrypt('1234567890'),
                'address' => credential_encrypt('Noida'),
                'pincode' => credential_encrypt('123456'),
                'gender' => 'M',
                'status' => 'Y',
                'usertype' => $usertype->id,
                'employee_code' => $employeeCode,
                'bank_name' => credential_encrypt('SBI'),
                'account_no' => credential_encrypt('1234567890'),
                'ifsc_code' => credential_encrypt('SBI123456789'),
                'account_holder_name' => credential_encrypt('Employee Admin'),
                'bank_branch' => credential_encrypt('Noida'),
                'reportingto' => 0,
                'adhar_no' => credential_encrypt('123456789012'),
                'pan_no' => credential_encrypt('ABCDE1234F'),
                'zone_id' => 1,
                'is_admin' => 'Y',
            ]);
                $lastUserId = DB::table('users')->select('id')->where('name',credential_encrypt('Employee Admin'))->first();
            $UserRoleAssign = DB::table('model_has_roles')->insert([
                'role_id' => $role->id,
                'model_type' => 'App\Models\User',
                'model_id' => $lastUserId->id
            ]);
            $Permission = DB::table('permissions')->select('id')->whereIn('name', ['Dashboard.view','Sell now.view','Users.view','Users.edit','Users.upload','Users.delete','Roles Master.view','Roles Master.edit','Roles Master.upload','Roles Master.delete','AccessControl.view','AccessControl.edit','AccessControl.upload','AccessControl.delete','Policy Status Report.view','Policy Status Report.edit','Policy Status Report.upload','Policy Status Report.delete','Policy Report Filter Master.view','Policy Report Filter Master.edit','Policy Report Filter Master.upload','Policy Report Filter Master.delete','Template List.view','Template List.upload','Template List.edit','Template List.delete','Renewal.delete','Renewal.edit','Renewal.upload','Renewal.view','MISP Utility.delete','MISP Utility.edit','MISP Utility.upload','MISP Utility.view','OEM Onboarding.delete','OEM Onboarding.edit','OEM Onboarding.upload','OEM Onboarding.view','MISP Onboarding.delete','MISP Onboarding.edit','MISP Onboarding.upload','MISP Onboarding.view','Branch Onboarding.delete','Branch Onboarding.upload','Branch Onboarding.edit','Branch Onboarding.view','Delegate.delete','Delegate.edit','Delegate.upload','Delegate.view','Login History.delete','Login History.edit','Login History.upload','Login History.view','Offline Excel Configurator.delete','Offline Excel Configurator.edit','Offline Excel Configurator.upload','Offline Excel Configurator.view','Offline Excel Keys.delete','Offline Excel Keys.edit','Offline Excel Keys.upload','Offline Excel Keys.view','POS ic mapping.delete','POS ic mapping.edit','POS ic mapping.upload','POS ic mapping.view','Corporate Onboarding.delete','Corporate Onboarding.edit','Corporate Onboarding.upload','Corporate Onboarding.view','Visibility Report.delete','Visibility Report.edit','Visibility Report.upload','Visibility Report.view','Blog & Videos.delete','Blog & Videos.edit','Blog & Videos.upload','Blog & Videos.view','Broker Details.delete','Broker Details.edit','Broker Details.upload','Broker Details.view','Change Log.delete','Change Log.edit','Change Log.upload','Change Log.view','Commission Utility.delete','Commission Utility.edit','Commission Utility.upload','Commission Utility.view','Theme Configurator.delete','Theme Configurator.edit','Theme Configurator.upload','Theme Configurator.view','profile.delete','profile.edit','profile.view','profile.upload','Offline Policy Upload.delete','Offline Policy Upload.edit','Offline Policy Upload.upload','Offline Policy Upload.view','MIS Reports.delete','MIS Reports.edit','MIS Reports.upload','MIS Reports.view','Report.delete','Report.edit','Report.upload','Report.view','Downloaded Reports.delete','Downloaded Reports.edit','Downloaded Reports.upload','Downloaded Reports.view','Report Scheduler.delete','Report Scheduler.edit','Report Scheduler.upload','Report Scheduler.view','Policy Status.view','Policy Status.edit','Policy Status.upload','Policy Status.delete','Offline Excel Configurator.view','Offline Excel Configurator.edit','Offline Excel Configurator.upload','Offline Excel Configurator.delete','User Creation.view','User Creation.edit','User Creation.upload','User Creation.delete','Report Template List.view','Report Template List.edit','Report Template List.upload','Report Template List.delete','MIS Configurator.view','MIS Configurator.edit','MIS Configurator.upload','MIS Configurator.delete','Create FAQ.view','Create FAQ.edit','Create FAQ.upload','Create FAQ.delete'])->get(); //
            foreach ($Permission as $key => $value) {

                $dashboardPermission = DB::table('role_has_permissions')->insert([
                    'role_id' => $role->id,
                    'permission_id' => $value->id
                ]);
            }
            foreach ($lob as $l)
            {
                $userLobRelation = DB::table('user_lob_relation')->insert([
                    'user_id' => $lastUserId->id,
                    'lob_id' => $l->id,
                    'created_at' => now(),
                ]);
            }
        }


    }
}
