<?php

namespace Database\Seeders;

use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class EmailTemplateSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('template_master')->insert([


            'title' => 'Please Add Email Template',
            'dlt_id' => '1234',
            'alias' => 'add_email_template',
            'content' => 'Please Add Email Template',
            'communication_type' => 'email',
            'event' => 'add_email_template',
            'status' => 'Y',

        ]);
    }
}
