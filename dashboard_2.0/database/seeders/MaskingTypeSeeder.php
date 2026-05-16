<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class MaskingTypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('masking_type')->insert([
            [
                'mask_name' => "Address",
                'mongo_key' => 'address_line_1',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'mask_name' => "Adhaar",
                'mongo_key' => 'addhar_no',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'mask_name' => "Pan",
                'mongo_key' => 'pan_no',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'mask_name' => "Mobile",
                'mongo_key' => 'proposer_mobile',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'mask_name' => "DOB",
                'mongo_key' => 'proposer_dob',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'mask_name' => "Alphabetic",
                'mongo_key' => 'proposer_name',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'mask_name' => "Email",
                'mongo_key' => 'proposer_emailid',
                'created_at' => now(),
                'updated_at' => now(),
            ]
        ]);
    }
}
