<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class VehicleTypeRangesSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        // range_type_idd
        $type = [
            [
                'range_type_id' => 1,
                'range' => 'upto 6',
                'vehicle_type_id' => 3
            ],
            [
                'range_type_id' => 1,
                'range' => 'above 6',
                'vehicle_type_id' => 3
            ],
            [
                'range_type_id' => '2',
                'range' => 'Pickup 3W',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '2',
                'range' => 'Pickup 4W and above',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '1/1/2500',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '2501 - 3500',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '3501 - 7500',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '7501 - 12000',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '12001 - 16000',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '16001 - 40000',
                'vehicle_type_id' => 4
            ],
            [
                'range_type_id' => '3',
                'range' => '40001 - 999999',
                'vehicle_type_id' => 4
            ]
        ];

        DB::table('vehicle_type_ranges')->insert($type);
    }
}
