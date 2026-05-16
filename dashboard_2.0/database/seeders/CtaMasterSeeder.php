<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;


class CtaMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('cta_master')->insert([
            [
                'stage' => 1,
                'cta_name' => 'quote_url',
                'redirection_url' => '',
                'lob' => 1,
                'lob_name' => 'CAR',
                'stage_name' => 'Quote',
            ],
            [
                'stage' => 3,
                'cta_name' => 'proposal_url',
                'redirection_url' => '',
                'lob' => 1,
                'lob_name' => 'CAR',
                'stage_name' => 'Proposal Pending',
            ],
            [
                'stage' => 4,
                'cta_name' => 'proposal_url',
                'redirection_url' => '',
                'lob' => 1,
                'lob_name' => 'CAR',
                'stage_name' => 'Payment Pending',
            ],
            [
                'stage' => 5,
                'cta_name' => 'proposal_url',
                'redirection_url' => '',
                'lob' => 1,
                'lob_name' => 'CAR',
                'stage_name' => 'Booking Pending',
            ],
            [
                'stage' => 6,
                'cta_name' => 'policy_doc_path',
                'redirection_url' => '',
                'lob' => 1,
                'lob_name' => 'CAR',
                'stage_name' => 'Issued',
            ],
            [
                'stage' => 1,
                'cta_name' => 'quote_url',
                'redirection_url' => '',
                'lob' => 2,
                'lob_name' => 'BIKE',
                'stage_name' => 'Quote',
            ],
            [
                'stage' => 3,
                'cta_name' => 'proposal_url',
                'redirection_url' => '',
                'lob' => 2,
                'lob_name' => 'BIKE',
                'stage_name' => 'Proposal Pending',
            ],
            [
                'stage' => 4,
                'cta_name' => 'proposal_url',
                'redirection_url' => '',
                'lob' => 2,
                'lob_name' => 'BIKE',
                'stage_name' => 'Payment Pending',
            ],
            [
                'stage' => 6,
                'cta_name' => 'policy_doc_path',
                'redirection_url' => '',
                'lob' => 2,
                'lob_name' => 'BIKE',
                'stage_name' => 'Issued',

            ],
            [
                'stage' => 5,
                'cta_name' => 'proposal_url',
                'redirection_url' => '',
                'lob' => 2,
                'lob_name' => 'BIKE',
                'stage_name' => 'Booking Pending',
            ],
        ]);
    }
}
