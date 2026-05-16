<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class FuelTypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $type = [
            [
                'fuel_type' => 'Petrol'
            ],
            [
                'fuel_type' => 'Diesel'
            ],
            [
                'fuel_type' => 'CNG'
            ],
            [
                'fuel_type' => 'LPG'
            ],
            [
                'fuel_type' => 'Electric'
            ]
        ];

        DB::table('fuel_type')->insert($type);
    }
}
