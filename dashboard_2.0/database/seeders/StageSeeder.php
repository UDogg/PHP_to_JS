<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class StageSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('stage_master')->insert([
            [
                "stage_name" => "Quote",
                "priority" => 1,
                "sub_stage_name" => ",18",
                "created_at" => "2024-06-28 07:20:47",
                "updated_at" => "2024-09-30 08:09:10",
                "deleted_at" => null
              ],
                    [
                "stage_name" => "Rider",
                "priority" => 2,
                "sub_stage_name" => ",15",
                "created_at" => "2024-06-28 07:20:56",
                "updated_at" => "2024-09-30 08:09:16",
                "deleted_at" => null
              ],
                [
                "stage_name" => "Proposal Pending",
                "priority" => 3,
                "sub_stage_name" => ",17",
                "created_at" => "2024-06-28 07:21:21",
                "updated_at" => "2024-09-30 08:09:22",
                "deleted_at" => null
              ],
                [
                "stage_name" => "Payment Pending",
                "priority" => 4,
                "sub_stage_name" => ",16,5",
                "created_at" => "2024-06-28 07:21:32",
                "updated_at" => "2024-09-30 08:09:31",
                "deleted_at" => null
              ],
                [
                "stage_name" => "Booking Pending",
                "priority" => 5,
                "sub_stage_name" => ",6",
                "created_at" => "2024-06-28 07:21:39",
                "updated_at" => "2024-09-30 08:09:31",
                "deleted_at" => null
              ],
                [
                "stage_name" => "Issued",
                "priority" => 6,
                "sub_stage_name" => "8,11,9,12,13,7",
                "created_at" => "2024-06-28 07:21:45",
                "updated_at" => "2024-09-30 08:09:26",
                "deleted_at" => null
                ]
            ]);
    }
}
