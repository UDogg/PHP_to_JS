<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class VehicleSubTypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $type = [
            [
                'name' => 'Taxi',
                'vehicle_type_id' => 3
            ],
            [
                'name' => 'Auto Rickshaw',
                'vehicle_type_id' => 3
            ],
            [
                'name' => 'E Rickshaw',
                'vehicle_type_id' => 3
            ],
            [
                'name' => 'School bus',
                'vehicle_type_id' => 3
            ],
            [
                'name' => 'Passenger bus',
                'vehicle_type_id' => 3
            ],
            [
                'name' => 'AGRICULTURAL-TRACTOR',
                'vehicle_type_id' => 5
            ],
            [
                'name' => 'MISCELLANEOUS-CLASS',
                'vehicle_type_id' => 5
            ],
            [
                'name' => 'PICK UP/DELIVERY/REFRIGERATED VAN',
                'vehicle_type_id' => 4
            ],
            [
                'name' => 'DUMPER/TIPPER',
                'vehicle_type_id' => 4
            ],
            [
                'name' => 'TRUCK',
                'vehicle_type_id' => 4
            ],
            [
                'name' => 'TRACTOR',
                'vehicle_type_id' => 4
            ],
            [
                'name' => 'TANKER/BULKER',
                'vehicle_type_id' => 4
            ]
        ];

        DB::table('vehicle_sub_type')->insert($type);
    }
}
