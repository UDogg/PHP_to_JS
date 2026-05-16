<?php

namespace Database\Seeders;

use App\Models\User;
use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Str;

class UsersTableSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
//        DB::statement('alter table users  AUTO_INCREMENT = 1');
        DB::table('users')->insert([
            'name' => credential_encrypt('Super Admin'),
            'email' => credential_encrypt('super_admin@fyntune.com'),
            'password' => Hash::make('Admin@123'),
            'mobile' => credential_encrypt('1234567890'),
            'address' => credential_encrypt('Noida'),
            'pincode' => credential_encrypt('123456'),
            'gender' => 'M',
            'status' => 'Y',
            'username' => credential_encrypt('super_admin'),
            'is_admin' => 'Y',


            'remember_token' => Str::random(10),
        ]);
        $role = DB::table('roles')->select('id')->where('name', 'Super Admin')->first();

        $UserRoleAssign = DB::table('model_has_roles')->insert([
            'role_id' => $role->id,
            'model_type' => 'App\Models\User',
            'model_id' => 1
        ]);



    }
}
