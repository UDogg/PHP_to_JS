<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class BranchMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('branch_master')->insert([
            [
                'branch_name' => 'delhi',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'branch_name' => 'pune',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'branch_name' => 'mumbai',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'branch_name' => 'navi-mumbai',
                'created_at' => now(),
                'updated_at' => now(),
            ]
        ]);
    }
}
