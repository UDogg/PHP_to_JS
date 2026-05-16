<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class ClaimMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('claim_stage_master')->insert([
            [

                'stage_name' => 'Intimation Details',
            ],
            [

                'stage_name' => 'Surveyor Deputation',
            ],
            [

                'stage_name' => 'Surveyor Completion',
            ],
            [

                'stage_name' => 'Work Approval',
            ],
            [

                'stage_name' => 'Delivery Order',
            ],
            [

                'stage_name' => 'Settled',
            ],
            [

                'stage_name' => 'Reject',
            ],
            [

                'stage_name' => 'Withdrawal',
            ]
        ]);
    }
}
