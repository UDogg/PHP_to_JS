<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class UsertypeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
//        DB::statement('alter table usertypes  AUTO_INCREMENT = 1');

        $usertypeArr = [
            [
                'name' => 'Employee',
                'Identifier' => 'E',
                'is_visible' => 'Y'
            ],
            [
                'name' => 'POS',
                'Identifier' => 'P',
                'is_visible' => 'Y'
            ],
            [
                'name' => 'Partner',
                'Identifier' => 'Partner',
                'is_visible' => 'Y'
            ],
            [
                'name' => 'B2C',
                'Identifier' => 'b2c',
                'is_visible' => 'Y'
            ],
            [
                'name' => 'Customer',
                'Identifier' => 'U',
                'is_visible' => 'Y'
            ],
            [
                'name' => 'MISP',
                'Identifier' => 'MISP',
                'is_visible' => 'Y'
            ],
            [
                'name' => 'SP',
                'Identifier' => 'SP',
                'is_visible' => 'Y'
            ],
        ];

        DB::table('usertypes')->insert($usertypeArr);
    }
}
