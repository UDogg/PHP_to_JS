<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class PolicyStatusColumnMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('policystatus_column_master')->insert([
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_tenture_days",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Policy Days",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "3"
            ],
            [
                "column_name" => "trace_id_created_on",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",20"
            ],
            [
                "column_name" => "non_electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",20"
            ],
            [
                "column_name" => "cng_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age_slab",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_tp",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",20"
            ],
            [
                "column_name" => "addon_plan",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Trace ID",
                "lob" => "8,2,6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_registration_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle No.",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "journey_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_make",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Company",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_model",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Model",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_version",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Version",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_cubic_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_fuel_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Fuel",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_seating_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_built_up",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_gvw",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Type",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_registration_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_expiry_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_ncb",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_manufacture_year",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_claim",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_body_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "gender_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_1",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_2",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_3",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "engine_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "chassis_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relationship",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_prev_company",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "inspection_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_period",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "prev_policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_additional_covers",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_accessories",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_discounts",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "CKYC Status",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addhar_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pan_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_order_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "corp_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "campaign_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_non_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_cng",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pa_to_owner_driver",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rto_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_vehicle",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_total",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nonelectrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ll_paid_driver_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zd_previous_policy_addon",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_breakup",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2c",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2b",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_reference_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_meta_data",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_verified",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_details_rejected",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type_value",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_extras",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rollover_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "enquiry_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => null,
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_tenture_days",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "policy  dats",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "trace_id_created_on",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "non_electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",7"
            ],
            [
                "column_name" => "electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "cng_cover_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",7"
            ],
            [
                "column_name" => "vehicle_age_slab",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "cng_tp",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "addon_plan",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Trace ID",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5,6,7,8,17,16"
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Name",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5,6,7,8,17,16"
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Mobile No.",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5,6,7,8,17,16"
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Customer Email",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5,6,7,17"
            ],
            [
                "column_name" => "vehicle_registration_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "journey_type",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_make",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Company",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_model",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Model",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_version",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Version",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_cubic_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_fuel_type",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Vehicle Fuel",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "vehicle_seating_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_built_up",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_gvw",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Policy Type",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",8"
            ],
            [
                "column_name" => "vehicle_registration_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_expiry_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_ncb",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_manufacture_year",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_claim",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_body_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Insurer",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5,6,7,8,17"
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "gender_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Total Premium",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5,6,7,8"
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Policy Start Date",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",8"
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_1",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",16"
            ],
            [
                "column_name" => "address_line_2",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_3",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "engine_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "chassis_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relationship",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_prev_company",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "inspection_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_period",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "prev_policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",8"
            ],
            [
                "column_name" => "product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_additional_covers",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "selected_accessories",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_discounts",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Ckyc Status",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5,6,7,8,17,3,16"
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Policy Stage",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5,8"
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Updated Time",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5,6,7,8,17,16"
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Seller Name",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addhar_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pan_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_order_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",7"
            ],
            [
                "column_name" => "payment_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "corp_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "campaign_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_non_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_cng",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pa_to_owner_driver",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rto_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_vehicle",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_total",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nonelectrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ll_paid_driver_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zd_previous_policy_addon",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source_type",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_breakup",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2c",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2b",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_reference_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_meta_data",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_verified",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_details_rejected",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type_value",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_extras",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rollover_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "enquiry_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "actual_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Section",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",18"
            ],
            [
                "column_name" => "enquiry_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "dashboard_user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Trace ID",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,4,5,6,7"
            ],
            [
                "column_name" => "proposal_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "IC Name",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",7,8"
            ],
            [
                "column_name" => "company_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Name",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,4,5,6,7,8"
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Mobile No.",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,4,5,6,7,8"
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Email",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",6,7,8"
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_pan_card",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_aadhar_card",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_annual_income",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_marital_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_alternate_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_occupation",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_pre_existing_diseases",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Ckyc Status",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",6,7,8"
            ],
            [
                "column_name" => "health_plan_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "insured_member_count",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Insured Member",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,4,5,6,7"
            ],
            [
                "column_name" => "health_all_members",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Total Premium",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5,6,7,8"
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "top_up_deductible",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Policy Start Date",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",8"
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "health_pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Pin Code",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5,6,7"
            ],
            [
                "column_name" => "address",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_contact",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relation",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_details_page_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Updated Time",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,4,5,6,7"
            ],
            [
                "column_name" => "proposal_lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pg_response",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quotes_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Payment Status",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",7"
            ],
            [
                "column_name" => "underwriting_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_frequency",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Seller Name",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,4,5,6,7"
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_corporate_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "customer_rating",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "customer_feedback",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Section",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Trace ID",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "trace_id_created_on",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "non_electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age_slab",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_plan",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Name",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5"
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Customer Mobile No.",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3,5"
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Customer Email",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5"
            ],
            [
                "column_name" => "vehicle_registration_number",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Vehicle No.",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "journey_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_make",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Company",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_model",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Model",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_version",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Version",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_cubic_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_fuel_type",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Vehicle Fuel",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_seating_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_built_up",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_gvw",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Type",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_registration_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_expiry_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_ncb",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_manufacture_year",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_claim",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_body_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" =>"1,3,4,5,6,7"
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "gender_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Total Premium",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",5"
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Policy Start Date",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Policy End Date",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_1",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_2",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_3",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "engine_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "chassis_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relationship",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_prev_company",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "inspection_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "Policy No.",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_period",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "prev_policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_additional_covers",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_accessories",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_discounts",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => "CKYC Status",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ",3"
            ],
            [
                "column_name" => "renewal_redirection_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "Y",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addhar_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pan_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_order_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "corp_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "campaign_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "encrypted_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_non_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_cng",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pa_to_owner_driver",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rto_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_vehicle",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_total",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nonelectrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ll_paid_driver_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zd_previous_policy_addon",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_breakup",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2c",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2b",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_reference_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_meta_data",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_verified",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_details_rejected",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type_value",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_extras",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rollover_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Trace ID",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "policy_tenture_days",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id_created_on",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "non_electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age_slab",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_tp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_plan",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_registration_number",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Vehicle No.",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "journey_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_make",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Vehicle Company",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_model",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Model",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_version",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Version",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_cubic_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_fuel_type",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Vehicle Fuel",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_seating_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_built_up",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_gvw",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Policy Type",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "vehicle_registration_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_expiry_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_ncb",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_manufacture_year",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_claim",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_body_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "gender_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_1",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_2",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_3",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "engine_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "chassis_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relationship",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_prev_company",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "inspection_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_period",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "prev_policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_additional_covers",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_accessories",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_discounts",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "CKYC Status",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "Y",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => "1,3,4,5,6,7"
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addhar_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pan_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_order_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "corp_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "campaign_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "encrypted_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_non_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_cng",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pa_to_owner_driver",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rto_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_vehicle",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_total",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nonelectrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ll_paid_driver_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zd_previous_policy_addon",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_breakup",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2c",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2b",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_reference_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_meta_data",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_verified",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_details_rejected",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type_value",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_extras",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rollover_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_tenture_days",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id_created_on",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "non_electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_age_slab",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_tp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_plan",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "migration_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "migration_comment",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_registration_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle No.",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "journey_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_make",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Company",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_model",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Model",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_version",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Version",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_cubic_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_fuel_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Vehicle Fuel",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_seating_capacity",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_built_up",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_gvw",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Type",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_registration_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_expiry_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_ncb",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_manufacture_year",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_claim",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "vehicle_body_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "gender_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_net_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_1",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_2",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address_line_3",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "engine_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "chassis_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa_policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relationship",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_age",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tp_prev_company",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "breakin_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "inspection_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_period",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "prev_policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "od_discount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_additional_covers",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_accessories",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_discounts",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "CKYC Status",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addhar_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pan_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_order_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "corp_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "campaign_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_offline_entry",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_offline_entry",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_offline_entry",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_offline_entry",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_offline_entry",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "encrypted_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_non_electrical",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_cng",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cng_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cpa",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pa_to_owner_driver",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rto_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rto_city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_category_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_vehicle",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "idv_total",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "electrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nonelectrical_accessories_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zero_dep_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ll_paid_driver_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zd_previous_policy_addon",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_od_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "basic_tp_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_breakup",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2c",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_redirection_url_b2b",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_reference_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_meta_data",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_verified",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_ckyc_details_rejected",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_type_value",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_extras",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rollover_renewal",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_via_whatapp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renewed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "agent_pos_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "employee_pos_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "migration_uploaded_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "migration_uploaded_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_journeys",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "enquiry_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "actual_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "enquiry_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "dashboard_user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_pan_card",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_aadhar_card",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_annual_income",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_marital_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_alternate_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_occupation",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_pre_existing_diseases",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "CKYC Status",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "health_plan_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Type",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "insured_member_count",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "health_all_members",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "top_up_deductible",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "health_pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_contact",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "nominee_relation",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_details_page_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pg_response",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quotes_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "underwriting_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_frequency",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_corporate_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "customer_rating",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "customer_feedback",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "actual_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_request_response_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_stage_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Trace ID",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => "Customer ID",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "proposal_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_date",
                "is_default" => "N",
                "is_visible" => "Y",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => ""
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sp_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "application_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium'",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_precentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "reference_by",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pg_response",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "annual_income",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_failure_remark",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "medical_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_corporate_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rider_details",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "benefit_payouts",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_upto",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_pay_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "education",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "occupation",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "term_tobacco_habit",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "current_page_link",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "term_redirection_link",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "underwriting_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quotes_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_pdf",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_receipt_pdf",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "9",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "actual_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "enquiry_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "dashboard_user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Trace ID",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_logo_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pet_details",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_details_page_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "thanku_page_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_pan_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_aadhar",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ckyc_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quotes_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_frequency",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_request",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_response",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "insurance_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_source",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_corporate_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_business_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "customer_rating",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "customer_feedback",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_offline_entry",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_business_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_renew",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_broker_offline_upload",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "11",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "0",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "actual_trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "section",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Section",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "updated_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "created_at",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "addon_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "address",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "annual_income",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "application_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "base_premium",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Net Premium",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "benefit_payouts",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "branch_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "channel_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "city",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_alias",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_corporate_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_domain_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "company_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "IC Name",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "cover_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "current_page_link",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "discount_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "education",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "first_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "hypothecation_to",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "is_financed",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "last_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lastupdated_time",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "lead_stage_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "medical_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_percentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "ncb_precentage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "occupation",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "owner_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_mode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_receipt_pdf",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_request_response_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "payment_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pg_response",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pincode",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_doc_path",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_end_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy End Date",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_failure_remark",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy No.",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_start_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Start Date",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "policy_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Total Premium",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "premium_pay_term",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_insurer",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "previous_policy_number",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "primary_insured_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_no",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_pdf",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposal_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_dob",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_emailid",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Email",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_gender",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Mobile No.",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "proposer_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Customer Name",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quote_url",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "quotes_date_timestamp",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "reference_by",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "region_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "renewal_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rider_details",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sales_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "selected_addons",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Mobile No.",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Name",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_type",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Seller Type",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "seller_username",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sp_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "state",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sub_product_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "sum_assured",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "tax_amount",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "term_redirection_link",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "term_tobacco_habit",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "trace_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Trace ID",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_date",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "transaction_stage",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => "Policy Stage",
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "underwriting_status",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "user_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_id",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "zone_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "10",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_name",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_mobile",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "pos_code",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "rm_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "1",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "2",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "3",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "4",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "5",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "6",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ],
            [
                "column_name" => "supervisor_email",
                "is_default" => "N",
                "is_visible" => "N",
                "alias" => null,
                "lob" => "8",
                "created_at" => null,
                "updated_at" => null,
                "stage" => null
            ]
        ]);
    }
}
