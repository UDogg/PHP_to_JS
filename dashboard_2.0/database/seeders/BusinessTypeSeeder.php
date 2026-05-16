<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class BusinessTypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $type = [
            [
                'name' => 'Rollover'
            ],
            [
                'name' => 'New'
            ],
            [
                'name' => 'Renewal'
            ],
            [
                'name' => 'Breakin'
            ]
        ];

        DB::table('business_type')->insert($type);
    }
}
