<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class BrokerSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('broker')->insert([
            'broker_name'=>'Admin',
            'category'=>'direct',
            'cin_no'=>'SDER5678',
            'address' =>'Noida',
            'contact_no' =>'8910598745',
            'email'=>'abc@fyntune.com',
            'irdia_registration_no'=>'123',
            'sign_in_option' => 'email_otp,password',
            'city' => '1',
            'state' => '1',
            'status'=>'Y',
            'master_otp' => '123456'
        ]);
    }
}
