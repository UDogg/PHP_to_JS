<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class QualificationSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('qualification_master')->insert([[

        'qualification_name' => 'HSC',
          'status' => 'Y'
        ],
            [

                'qualification_name' => 'SSC',
                'status' => 'Y'
            ],
            [

                'qualification_name' => 'Diploma',
                'status' => 'Y'
            ],
            [

                'qualification_name' => 'Graduation',
                'status' => 'Y'
            ],
            [

                'qualification_name' => 'Post Graduation',
                'status' => 'Y'
            ],

            [

                'qualification_name' => 'Other',
                'status' => 'Y'
            ]
        ]);
    }
}
