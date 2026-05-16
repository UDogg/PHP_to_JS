<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class VehicleTypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $type = [
            [
                'name' => 'Car'
            ],
            [
                'name' => 'Bike'
            ],
            [
                'name' => 'PCV'
            ],
            [
                'name' => 'GCV'
            ],
            [
                'name' => 'Miscd'
            ]
        ];

        DB::table('vehicle_type')->insert($type);
    }
}
