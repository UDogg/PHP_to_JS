<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;

class PosAdminUserSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $usertype = DB::table('usertypes')->select('id')->where('Identifier', 'P')->first();
        $employeeCode = 2222;
        $lob = DB::table('lob_master')->select('id')->whereIn('lob', ['CAR','GCV','PCV','health','travel','super top up','BIKE','MISC','term','investment'])->get();
        $lastUserId = DB::table('users')->select('id')->where('name',credential_encrypt('Posp Admin'))->first();
        $role = DB::table('roles')->select('id')->where('name', 'Posp Admin')->first();


        if(empty($lastUserId))
        {
            $usercreate = DB::table('users')->insert([
                'name' => credential_encrypt('Posp Admin'),
                'email' => credential_encrypt('posp_admin@fyntune.com'),
                'password' => Hash::make('Admin@123'),
                'username' => credential_encrypt('posp_admin'),
                'mobile' => credential_encrypt('1234567890'),
                'address' => credential_encrypt('Noida'),
                'pincode' => credential_encrypt('123456'),
                'gender' => 'M',
                'status' => 'Y',
                'is_admin' => 'Y',
                'usertype' => $usertype->id,
                'employee_code' => '',
                'bank_name' => credential_encrypt('SBI'),
                'account_no' => credential_encrypt('1234567890'),
                'ifsc_code' => credential_encrypt('SBI123456789'),
                'account_holder_name' => credential_encrypt('Posp_Admin'),
                'bank_branch' => credential_encrypt('Noida'),
                'reportingto' => 0,
                'adhar_no' => credential_encrypt('123456789012'),
                'pan_no' => credential_encrypt('ABCDE1234F'),
                'pos_code' => 0000,
                'qualification' => 2,
                'zone_id' => 1
            ]);
            $lastUserId = DB::table('users')->select('id')->where('name',credential_encrypt('Posp Admin'))->first();
            $UserRoleAssign = DB::table('model_has_roles')->insert([
                'role_id' => $role->id,
                'model_type' => 'App\Models\User',
                'model_id' => $lastUserId->id
            ]);
            $Permission = DB::table('permissions')->select('id')->whereIn('name', ['Dashboard.view','Sell now.view','Users.view','Users.edit','Users.upload','Users.delete','Roles Master.view','Roles Master.edit','Roles Master.upload','Roles Master.delete','AccessControl.view','AccessControl.edit','AccessControl.upload','AccessControl.delete','Policy Status Report.view','Policy Status Report.edit','Policy Status Report.upload','Policy Status Report.delete','Policy Report Filter Master.view','Policy Report Filter Master.edit','Policy Report Filter Master.upload','Policy Report Filter Master.delete'])->get();
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
