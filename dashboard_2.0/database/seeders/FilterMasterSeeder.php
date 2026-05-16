<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class FilterMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('policy_status_filter_master')->insert([
            [
            'filtername' => 'Date',
            'type' => 3,
            'key' => '',
            'value' => '',
            'lob' => 5,
            "column" => null,
            'created_at'  => now()

            ],
            [
                'filtername' => 'Date',
                'type' => 3,
                'key' => '',
                'value' => '',
                'lob' => 6,
                "column" => null,
                'created_at'  => now()
            ],
            [
                'filtername' => 'LOB',
                'type' => 2,
                'key' => 'PCV',
                'value' => 'PCV',
                'lob' => 5,
                "column" => null,
                'created_at'  => now()
            ],
            [
                'filtername' => 'LOB',
                'type' => 2,
                'key' => 'health',
                'value' => 'Health',
                'lob' => 6,
                "column" => null,
                'created_at'  => now()
            ],
            [
                'filtername' => 'LOB',
                'type' => 4,
                'key' => 'Car',
                'value' => 'Car',
                'lob' => 1,
                "column" => null,
                'created_at'  => now()
            ],
            [
                'filtername' => 'LOB',
                'type' => 4,
                'key' => 'bike',
                'value' => 'bike',
                'lob' => 2,
                "column" => null,
                'created_at'  => now()
            ]

        ]);

    }
}
