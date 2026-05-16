<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class SubStageSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('sub_stage_master')->insert([
          [

            "sub_stage_name" => "Inspection Accept",
            "is_renewal" => null,
            "created_at" => now(),
          ],
                [
            "sub_stage_name" => "Inspection Pending",
            "is_renewal" => "N",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Inspection Rejected",
            "is_renewal" => "N",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Lead Generation",
            "is_renewal" => "N",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Payment Failed",
            "is_renewal" => "N",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Payment Initiated",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Payment Received",
            "is_renewal" => "Y",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Payment Received, but pdf not generated",
            "is_renewal" => "Y",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Payment Success",
            "is_renewal" => "Y",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Policy Cancelled",
            "is_renewal" => "N",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Policy Issued",
            "is_renewal" => "Y",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Policy Issued pdf generated",
            "is_renewal" => "Y",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Policy Issued, but pdf not generated",
            "is_renewal" => "Y",
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Policy Rejected",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Product Details Page",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Proposal Accepted",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Proposal Drafted",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Quote - Buy Now",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Quote Redirect",
            "is_renewal" => null,
            "created_at" => now(),
          ],
            [
            "sub_stage_name" => "Underwriting Approval",
            "is_renewal" => null,
            "created_at" => now(),
          ]
        ]);
    }

}
