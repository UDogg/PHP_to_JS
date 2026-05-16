<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class RangesTypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $type = [
            [
                'name' => 'Seating Capacity'
            ],
            [
                'name' => 'Number of Wheels '
            ],
            [
                'name' => 'GVW Range'
            ]
        ];

        DB::table('ranges_type')->insert($type);
    }
}
