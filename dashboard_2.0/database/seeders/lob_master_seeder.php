<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class lob_master_seeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('lob_master')->insert([
            [
                'lob_name' => 'car 4W',
                'lob' => 'CAR',
                'frontend_url' => 'https://sandbox.fynity.in/motor/car/lead-page/'
            ],
            [
                'lob_name' => 'bike 2W',
                'lob' => 'BIKE',
                'frontend_url' => 'https://sandbox.fynity.in/motor/bike/lead-page/'
            ],
            [
                'lob_name' => 'miscellaneous',
                'lob' => 'MISC',
                'frontend_url' => 'https://sandbox.fynity.in/motor/cv/lead-page/'
            ],
            [
                'lob_name' => 'goods carring vehicle',
                'lob' => 'GCV',
                'frontend_url' => 'https://sandbox.fynity.in/motor/cv/lead-page/'
            ],
            [
                'lob_name' => 'Passsenger carring vehicle'
                , 'lob' => 'PCV',
                'frontend_url' => 'https://sandbox.fynity.in/motor/cv/lead-page/'
            ],
            [
                'lob_name' => 'health insurance',
                'lob' => 'health',
                'frontend_url' => ''
            ],
            [
                'lob_name' => 'travel insurance',
                'lob' => 'travel',
                'frontend_url' => ''
            ],
            [
                'lob_name' => 'super top up life insurance',
                'lob' => 'top_up',
                'frontend_url' => ''
            ],
            [
                'lob_name' => 'term insurance',
                'lob' => 'term',
                'frontend_url' => 'https://demo-term.fynity.in/'
            ],
            [
                'lob_name' => 'investment insurance',
                'lob' => 'investment',
                'frontend_url' => 'https://demo-investment.fynity.in/'
            ],
            [
                'lob_name' => 'pet',
                'lob' => 'pet',
                'frontend_url' => ''
            ],
            [
                'lob_name' => 'life insurance',
                'lob' => 'Life',
                'frontend_url' => 'https://demo-life.fynity.in/'
            ]
            ]);
    }
}
