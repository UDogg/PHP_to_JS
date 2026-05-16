<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class ZoneMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('zone_master')->insert([
            [
                "id" => 1,
                "office_zone" => "EAST",
                "office_name" => "",
                "parent_office" => "",
                "office_pincode" => "",
                "contact_phone" => "",
                "contact_email" => "",
                "address" => "",
                "created_at" => "2024-09-10 08:42:27",
                "updated_at" => "2024-09-10 08:42:27"
            ],
            [
                "id" => 2,
                "office_zone" => "WEST",
                "office_name" => "",
                "parent_office" => "",
                "office_pincode" => "",
                "contact_phone" => "",
                "contact_email" => "",
                "address" => "",
                "created_at" => "2024-09-10 08:42:35",
                "updated_at" => "2024-09-10 08:42:35"
            ],
            [
                "id" => 3,
                "office_zone" => "NORTH",
                "office_name" => "",
                "parent_office" => "",
                "office_pincode" => "",
                "contact_phone" => "",
                "contact_email" => "",
                "address" => "",
                "created_at" => "2024-09-10 08:42:39",
                "updated_at" => "2024-09-10 08:42:39"
            ]
        ]);
    }
}
