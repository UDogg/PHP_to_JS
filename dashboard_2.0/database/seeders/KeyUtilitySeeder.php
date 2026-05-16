<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class KeyUtilitySeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('key_utility')->insert([

  [
    "key" => "Customer Mobile",
    "created_at" => "2024-09-13 11:38:18",
    "updated_at" => "2024-09-25 11:09:08"
  ],
        [
    "key" => "Customer DOB",
    "created_at" => "2024-09-13 11:42:29",
    "updated_at" => "2024-09-13 11:42:29"
  ],
    [
    "key" => "Customer Name",
    "created_at" => "2024-09-13 11:46:41",
    "updated_at" => "2024-09-13 11:46:41"
  ],
    [
    "key" => "Customer Email ID",
    "created_at" => "2024-09-13 11:48:12",
    "updated_at" => "2024-09-13 11:48:12"
  ],
    [
    "key" => "Customer Gender",
    "created_at" => "2024-09-13 11:49:00",
    "updated_at" => "2024-09-13 11:49:00"
  ],
    [
    "key" => "Customer Address",
    "created_at" => "2024-09-13 11:50:48",
    "updated_at" => "2024-09-13 11:50:48"
  ],
    [
    "key" => "Customer City",
    "created_at" => "2024-09-13 11:51:24",
    "updated_at" => "2024-09-13 11:51:24"
  ],
    [
    "key" => "Customer PINCODE",
    "created_at" => "2024-09-13 11:52:50",
    "updated_at" => "2024-09-13 11:52:50"
  ],
    [
    "key" => "Customer State",
    "created_at" => "2024-09-13 11:53:31",
    "updated_at" => "2024-09-13 11:53:31"
  ],
    [
    "key" => "Customer first name",
    "created_at" => "2024-09-13 11:55:18",
    "updated_at" => "2024-09-13 11:55:18"
  ],
    [
    "key" => "Customer last Name",
    "created_at" => "2024-09-13 11:56:03",
    "updated_at" => "2024-09-13 11:56:03"
  ],
    [
    "key" => "Nominee Name",
    "created_at" => "2024-09-13 12:01:10",
    "updated_at" => "2024-09-13 12:01:10"
  ],
    [
    "key" => "Nominee Age",
    "created_at" => "2024-09-13 12:01:38",
    "updated_at" => "2024-09-13 12:01:38"
  ],
    [
    "key" => "Nominee relationship",
    "created_at" => "2024-09-13 12:02:12",
    "updated_at" => "2024-09-13 12:02:12"
  ],
    [
    "key" => "Nominee DOB",
    "created_at" => "2024-09-13 12:02:36",
    "updated_at" => "2024-09-13 12:02:36"
  ],
    [
    "key" => "Vehicle Registration Date",
    "created_at" => "2024-09-13 12:05:13",
    "updated_at" => "2024-09-13 12:05:13"
  ],
    [
    "key" => "Vehicle Registration Number",
    "created_at" => "2024-09-13 12:05:43",
    "updated_at" => "2024-09-13 12:05:43"
  ],
    [
    "key" => "Vehicle Make",
    "created_at" => "2024-09-13 12:06:18",
    "updated_at" => "2024-09-13 12:06:18"
  ],
    [
    "key" => "Vehicle Make",
    "created_at" => "2024-09-13 12:06:18",
    "updated_at" => "2024-09-13 12:06:18"
  ],
    [
    "key" => "Vehicle Model",
    "created_at" => "2024-09-13 12:06:38",
    "updated_at" => "2024-09-13 12:06:38"
  ],
    [
    "key" => "Vehicle Model",
    "created_at" => "2024-09-13 12:06:38",
    "updated_at" => "2024-09-13 12:06:38"
  ],
    [
    "key" => "Vehicle variant",
    "created_at" => "2024-09-13 12:07:32",
    "updated_at" => "2024-09-13 12:07:32"
  ],
    [
    "key" => "Vehicle variant",
    "created_at" => "2024-09-13 12:07:32",
    "updated_at" => "2024-09-13 12:07:32"
  ],
    [
    "key" => "RTO",
    "created_at" => "2024-09-13 12:08:09",
    "updated_at" => "2024-09-13 12:08:09"
  ],
    [
    "key" => "RTO",
    "created_at" => "2024-09-13 12:08:09",
    "updated_at" => "2024-09-13 12:08:09"
  ],
    [
    "key" => "Engine Number",
    "created_at" => "2024-09-13 12:08:54",
    "updated_at" => "2024-09-13 12:08:54"
  ],
    [
    "key" => "Engine Number",
    "created_at" => "2024-09-13 12:08:54",
    "updated_at" => "2024-09-13 12:08:54"
  ],
    [
    "key" => "Chassis Number",
    "created_at" => "2024-09-13 12:09:25",
    "updated_at" => "2024-09-13 12:09:25"
  ],
    [
    "key" => "Vehicle Fuel Type",
    "created_at" => "2024-09-13 12:09:50",
    "updated_at" => "2024-09-13 12:09:50"
  ],
    [
    "key" => "Vehicle Seating Capacity",
    "created_at" => "2024-09-14 10:52:29",
    "updated_at" => "2024-09-14 10:52:29"
  ],
    [
    "key" => "Vehicle Cubic Capacity",
    "created_at" => "2024-09-14 10:53:04",
    "updated_at" => "2024-09-14 10:53:04"
  ],
    [
    "key" => "Vehicle Manufacture Year",
    "created_at" => "2024-09-14 10:53:33",
    "updated_at" => "2024-09-14 10:53:33"
  ],
    [
    "key" => "Hypothecation",
    "created_at" => "2024-09-14 10:54:56",
    "updated_at" => "2024-09-14 10:54:56"
  ],
    [
    "key" => "Vehicle Age",
    "created_at" => "2024-09-14 10:55:32",
    "updated_at" => "2024-09-14 10:55:32"
  ],
    [
    "key" => "Vehicle Built Up",
    "created_at" => "2024-09-14 10:56:06",
    "updated_at" => "2024-09-14 10:56:06"
  ],
    [
    "key" => "Gross Vehicle Weight",
    "created_at" => "2024-09-14 10:56:59",
    "updated_at" => "2024-09-14 10:56:59"
  ],
    [
    "key" => "Vehicle Body Type",
    "created_at" => "2024-09-14 10:57:23",
    "updated_at" => "2024-09-14 10:57:23"
  ],
    [
    "key" => "Is Financed",
    "created_at" => "2024-09-14 10:57:45",
    "updated_at" => "2024-09-14 10:57:45"
  ],
    [
    "key" => "Trace Id",
    "created_at" => "2024-09-14 11:00:39",
    "updated_at" => "2024-09-14 11:00:39"
  ],
    [
    "key" => "Migration Status",
    "created_at" => "2024-09-14 12:59:35",
    "updated_at" => "2024-09-14 12:59:35"
  ],
    [
    "key" => "Migration Comment",
    "created_at" => "2024-09-14 12:59:58",
    "updated_at" => "2024-09-14 12:59:58"
  ],
    [
    "key" => "Section",
    "created_at" => "2024-09-14 13:00:42",
    "updated_at" => "2024-09-14 13:00:42"
  ],
    [
    "key" => "Product Name",
    "created_at" => "2024-09-14 13:01:24",
    "updated_at" => "2024-09-14 13:01:24"
  ],
    [
    "key" => "Business Type",
    "created_at" => "2024-09-14 13:02:45",
    "updated_at" => "2024-09-14 13:02:45"
  ],
    [
    "key" => "Journey Type",
    "created_at" => "2024-09-14 13:03:13",
    "updated_at" => "2024-09-14 13:03:13"
  ],
    [
    "key" => "Product Type",
    "created_at" => "2024-09-14 13:03:46",
    "updated_at" => "2024-09-14 13:03:46"
  ],
    [
    "key" => "Sub Product Type",
    "created_at" => "2024-09-14 13:04:55",
    "updated_at" => "2024-09-14 13:04:55"
  ],
    [
    "key" => "Ckyc Status",
    "created_at" => "2024-09-14 13:05:18",
    "updated_at" => "2024-09-14 13:05:18"
  ],
    [
    "key" => "Transaction Stage",
    "created_at" => "2024-09-14 13:05:52",
    "updated_at" => "2024-09-14 13:05:52"
  ],
    [
    "key" => "Source",
    "created_at" => "2024-09-14 13:06:26",
    "updated_at" => "2024-09-14 13:06:26"
  ],
    [
    "key" => "Sub Source",
    "created_at" => "2024-09-14 13:07:22",
    "updated_at" => "2024-09-14 13:07:22"
  ],
    [
    "key" => "Source Type",
    "created_at" => "2024-09-14 13:07:59",
    "updated_at" => "2024-09-14 13:07:59"
  ],
    [
    "key" => "Agent Type",
    "created_at" => "2024-09-14 13:09:20",
    "updated_at" => "2024-09-14 13:09:20"
  ],
    [
    "key" => "Agent Name",
    "created_at" => "2024-09-16 11:11:04",
    "updated_at" => "2024-09-16 11:11:04"
  ],
    [
    "key" => "Seller Mobile",
    "created_at" => "2024-09-16 11:12:58",
    "updated_at" => "2024-09-16 11:12:58"
  ],
    [
    "key" => "Agent Email",
    "created_at" => "2024-09-16 11:13:38",
    "updated_at" => "2024-09-16 11:13:38"
  ],
    [
    "key" => "Agent Id",
    "created_at" => "2024-09-16 11:15:07",
    "updated_at" => "2024-09-16 11:15:07"
  ],
    [
    "key" => "Agent Business Type",
    "created_at" => "2024-09-16 11:30:47",
    "updated_at" => "2024-09-16 11:30:47"
  ],
    [
    "key" => "Agent Business Code",
    "created_at" => "2024-09-16 11:31:39",
    "updated_at" => "2024-09-16 11:31:39"
  ],
    [
    "key" => "Agent Username",
    "created_at" => "2024-09-16 11:32:11",
    "updated_at" => "2024-09-16 11:32:11"
  ],
    [
    "key" => "Addhar Card No",
    "created_at" => "2024-09-16 11:32:50",
    "updated_at" => "2024-09-16 11:32:50"
  ],
    [
    "key" => "Pan Card Number",
    "created_at" => "2024-09-16 11:37:30",
    "updated_at" => "2024-09-16 11:37:30"
  ],
    [
    "key" => "Pos Code",
    "created_at" => "2024-09-16 11:38:05",
    "updated_at" => "2024-09-16 11:38:05"
  ],
    [
    "key" => "Agent Source",
    "created_at" => "2024-09-16 11:39:18",
    "updated_at" => "2024-09-16 11:39:18"
  ],
    [
    "key" => "Campaign Id",
    "created_at" => "2024-09-16 11:40:32",
    "updated_at" => "2024-09-16 11:40:32"
  ],
    [
    "key" => "Previous Policy Expiry Date",
    "created_at" => "2024-09-16 11:41:50",
    "updated_at" => "2024-09-16 11:41:50"
  ],
    [
    "key" => "Previous Policy Number",
    "created_at" => "2024-09-16 11:43:02",
    "updated_at" => "2024-09-16 11:43:02"
  ],
    [
    "key" => "Previous Ncb",
    "created_at" => "2024-09-16 11:43:40",
    "updated_at" => "2024-09-16 11:43:40"
  ],
    [
    "key" => "Previous Policy Start Date",
    "created_at" => "2024-09-16 11:44:30",
    "updated_at" => "2024-09-16 11:44:30"
  ],
    [
    "key" => "Previous Insurer",
    "created_at" => "2024-09-16 11:45:37",
    "updated_at" => "2024-09-16 11:45:37"
  ],
    [
    "key" => "Previous Policy Number",
    "created_at" => "2024-09-16 11:46:42",
    "updated_at" => "2024-09-16 11:46:42"
  ],
    [
    "key" => "Company Alias",
    "created_at" => "2024-09-16 11:48:26",
    "updated_at" => "2024-09-16 11:48:26"
  ],
    [
    "key" => "Company Name",
    "created_at" => "2024-09-16 11:49:29",
    "updated_at" => "2024-09-16 11:49:29"
  ],
    [
    "key" => "Policy Type",
    "created_at" => "2024-09-16 11:50:52",
    "updated_at" => "2024-09-16 11:50:52"
  ],
    [
    "key" => "Cover Amount",
    "created_at" => "2024-09-16 11:53:57",
    "updated_at" => "2024-09-16 11:53:57"
  ],
    [
    "key" => "Payment Order Id",
    "created_at" => "2024-09-16 11:54:39",
    "updated_at" => "2024-09-16 11:54:39"
  ],
    [
    "key" => "Payment Status",
    "created_at" => "2024-09-16 11:55:15",
    "updated_at" => "2024-09-16 11:55:15"
  ],
    [
    "key" => "Payment Time",
    "created_at" => "2024-09-16 11:55:52",
    "updated_at" => "2024-09-16 11:55:52"
  ],
    [
    "key" => "Policy Start Date",
    "created_at" => "2024-09-16 11:57:38",
    "updated_at" => "2024-09-16 11:57:38"
  ],
    [
    "key" => "Previous Policy Type",
    "created_at" => "2024-09-16 11:58:39",
    "updated_at" => "2024-09-16 11:58:39"
  ],
    [
    "key" => "Policy End Date",
    "created_at" => "2024-09-16 11:59:18",
    "updated_at" => "2024-09-16 11:59:18"
  ],
    [
    "key" => "Ncb Percentage",
    "created_at" => "2024-09-16 12:00:36",
    "updated_at" => "2024-09-16 12:00:36"
  ],
    [
    "key" => "OD Premium",
    "created_at" => "2024-09-16 12:01:19",
    "updated_at" => "2024-09-16 12:01:19"
  ],
    [
    "key" => "Ncb Discount",
    "created_at" => "2024-09-16 12:02:00",
    "updated_at" => "2024-09-16 12:02:00"
  ],
    [
    "key" => "TP Premium",
    "created_at" => "2024-09-16 12:03:01",
    "updated_at" => "2024-09-16 12:03:01"
  ],
    [
    "key" => "Addon Premium",
    "created_at" => "2024-09-16 12:03:54",
    "updated_at" => "2024-09-16 12:03:54"
  ],
    [
    "key" => "Breakin Number",
    "created_at" => "2024-09-16 12:04:42",
    "updated_at" => "2024-09-16 12:04:42"
  ],
    [
    "key" => "Breakin Status",
    "created_at" => "2024-09-16 12:05:22",
    "updated_at" => "2024-09-16 12:05:22"
  ],
    [
    "key" => "Policy Tenture Days",
    "created_at" => "2024-09-16 12:06:05",
    "updated_at" => "2024-09-16 12:06:05"
  ],
    [
    "key" => "Non Electrical Cover Amount",
    "created_at" => "2024-09-16 12:06:51",
    "updated_at" => "2024-09-16 12:06:51"
  ],
    [
    "key" => "Electrical Cover Amount",
    "created_at" => "2024-09-16 12:08:24",
    "updated_at" => "2024-09-16 12:08:24"
  ],
    [
    "key" => "Cng Cover Amount",
    "created_at" => "2024-09-16 12:08:54",
    "updated_at" => "2024-09-16 12:08:54"
  ],
    [
    "key" => "Vehicle Age Slab",
    "created_at" => "2024-09-16 12:09:20",
    "updated_at" => "2024-09-16 12:09:20"
  ],
    [
    "key" => "Cng Tp",
    "created_at" => "2024-09-16 12:10:11",
    "updated_at" => "2024-09-16 12:10:11"
  ],
    [
    "key" => "Addon Plan",
    "created_at" => "2024-09-16 12:11:26",
    "updated_at" => "2024-09-16 12:11:26"
  ],
    [
    "key" => "Previous Policy Trace Id",
    "created_at" => "2024-09-16 12:12:27",
    "updated_at" => "2024-09-16 12:12:27"
  ],
    [
    "key" => "Renewal Via Whatapp",
    "created_at" => "2024-09-16 12:13:05",
    "updated_at" => "2024-09-16 12:13:05"
  ],
    [
    "key" => "Rollover Renewal",
    "created_at" => "2024-09-16 12:13:41",
    "updated_at" => "2024-09-16 12:13:41"
  ],
    [
    "key" => "Is Renewal",
    "created_at" => "2024-09-16 12:14:14",
    "updated_at" => "2024-09-16 12:14:14"
  ],
    [
    "key" => "Ckyc Extras",
    "created_at" => "2024-09-16 12:14:46",
    "updated_at" => "2024-09-16 12:14:46"
  ],
    [
    "key" => "Ckyc Type Value",
    "created_at" => "2024-09-16 12:15:19",
    "updated_at" => "2024-09-16 12:15:19"
  ],
    [
    "key" => "Ckyc Type",
    "created_at" => "2024-09-16 12:15:52",
    "updated_at" => "2024-09-16 12:15:52"
  ],
    [
    "key" => "Is Ckyc Details Rejected",
    "created_at" => "2024-09-16 12:16:34",
    "updated_at" => "2024-09-16 12:16:34"
  ],
    [
    "key" => "Is Ckyc Verified",
    "created_at" => "2024-09-16 12:17:03",
    "updated_at" => "2024-09-16 12:17:03"
  ],
    [
    "key" => "Ckyc Meta Data",
    "created_at" => "2024-09-16 12:17:35",
    "updated_at" => "2024-09-16 12:17:35"
  ],
    [
    "key" => "Ckyc Reference Id",
    "created_at" => "2024-09-16 12:19:13",
    "updated_at" => "2024-09-16 12:19:13"
  ],
    [
    "key" => "Ckyc Number",
    "created_at" => "2024-09-16 12:19:36",
    "updated_at" => "2024-09-16 12:19:36"
  ],
    [
    "key" => "Lead Source",
    "created_at" => "2024-09-16 12:20:12",
    "updated_at" => "2024-09-16 12:20:12"
  ],
    [
    "key" => "Ncb Claim",
    "created_at" => "2024-09-16 12:21:26",
    "updated_at" => "2024-09-16 12:21:26"
  ],
    [
    "key" => "Proposal No",
    "created_at" => "2024-09-16 12:21:54",
    "updated_at" => "2024-09-16 12:21:54"
  ],
    [
    "key" => "Proposal No",
    "created_at" => "2024-09-16 12:25:43",
    "updated_at" => "2024-09-16 12:25:43"
  ],
    [
    "key" => "Premium Amount",
    "created_at" => "2024-09-16 12:26:42",
    "updated_at" => "2024-09-16 12:26:42"
  ],
    [
    "key" => "Base Premium",
    "created_at" => "2024-09-16 12:27:41",
    "updated_at" => "2024-09-16 12:27:41"
  ],
    [
    "key" => "Tax Amount",
    "created_at" => "2024-09-16 12:28:54",
    "updated_at" => "2024-09-16 12:28:54"
  ],
    [
    "key" => "Discount Amount",
    "created_at" => "2024-09-16 12:30:27",
    "updated_at" => "2024-09-16 12:30:27"
  ],
    [
    "key" => "Cpa Amount",
    "created_at" => "2024-09-16 12:32:14",
    "updated_at" => "2024-09-16 12:32:14"
  ],
    [
    "key" => "Proposal Date",
    "created_at" => "2024-09-16 12:34:38",
    "updated_at" => "2024-09-16 12:34:38"
  ],
    [
    "key" => "Cpa Policy Start Date",
    "created_at" => "2024-09-16 12:35:18",
    "updated_at" => "2024-09-16 12:35:18"
  ],
    [
    "key" => "Cpa Policy End Date",
    "created_at" => "2024-09-16 12:35:58",
    "updated_at" => "2024-09-16 12:35:58"
  ],
    [
    "key" => "Tp Start Date",
    "created_at" => "2024-09-16 12:36:24",
    "updated_at" => "2024-09-16 12:36:24"
  ],
    [
    "key" => "Tp End Date",
    "created_at" => "2024-09-16 12:36:58",
    "updated_at" => "2024-09-16 12:36:58"
  ],
    [
    "key" => "Tp Policy Number",
    "created_at" => "2024-09-16 12:37:54",
    "updated_at" => "2024-09-16 12:37:54"
  ],
    [
    "key" => "Tp Previous Company",
    "created_at" => "2024-09-16 12:38:37",
    "updated_at" => "2024-09-16 12:38:37"
  ],
    [
    "key" => "Inspection Date",
    "created_at" => "2024-09-16 12:39:14",
    "updated_at" => "2024-09-16 12:39:14"
  ],
    [
    "key" => "Owner Type",
    "created_at" => "2024-09-16 12:39:46",
    "updated_at" => "2024-09-16 12:39:46"
  ],
    [
    "key" => "Sales Date",
    "created_at" => "2024-09-16 12:40:22",
    "updated_at" => "2024-09-16 12:40:22"
  ],
    [
    "key" => "Transaction Date",
    "created_at" => "2024-09-16 12:41:13",
    "updated_at" => "2024-09-16 12:41:13"
  ],
    [
    "key" => "Policy Document Path",
    "created_at" => "2024-09-16 12:43:41",
    "updated_at" => "2024-09-16 12:43:41"
  ],
    [
    "key" => "Policy Period",
    "created_at" => "2024-09-16 12:44:53",
    "updated_at" => "2024-09-16 12:44:53"
  ],
    [
    "key" => "Zero Dep",
    "created_at" => "2024-09-16 12:45:30",
    "updated_at" => "2024-09-16 12:45:30"
  ],
    [
    "key" => "Od Discount",
    "created_at" => "2024-09-16 12:45:58",
    "updated_at" => "2024-09-16 12:45:58"
  ],
    [
    "key" => "Selected Addons",
    "created_at" => "2024-09-16 12:46:41",
    "updated_at" => "2024-09-16 12:46:41"
  ],
    [
    "key" => "Selected Additional Covers",
    "created_at" => "2024-09-16 12:47:33",
    "updated_at" => "2024-09-16 12:47:33"
  ],
    [
    "key" => "Selected Accessories",
    "created_at" => "2024-09-16 12:48:04",
    "updated_at" => "2024-09-16 12:48:04"
  ],
    [
    "key" => "Selected Discounts",
    "created_at" => "2024-09-16 12:48:40",
    "updated_at" => "2024-09-16 12:48:40"
  ],
    [
    "key" => "Proposal Url",
    "created_at" => "2024-09-16 12:53:40",
    "updated_at" => "2024-09-16 12:53:40"
  ],
    [
    "key" => "Quote Url",
    "created_at" => "2024-09-16 12:58:10",
    "updated_at" => "2024-09-16 12:58:10"
  ],
    [
    "key" => "Renewal Redirection Url",
    "created_at" => "2024-09-16 12:58:52",
    "updated_at" => "2024-09-16 12:58:52"
  ],
    [
    "key" => "Lastupdated Time",
    "created_at" => "2024-09-16 13:00:41",
    "updated_at" => "2024-09-16 13:00:41"
  ],
    [
    "key" => "IDV Electrical",
    "created_at" => "2024-09-16 13:01:25",
    "updated_at" => "2024-09-16 13:01:25"
  ],
    [
    "key" => "Idv Non Electrical",
    "created_at" => "2024-09-16 13:02:03",
    "updated_at" => "2024-09-16 13:02:03"
  ],
    [
    "key" => "IDV Cng",
    "created_at" => "2024-09-16 13:03:24",
    "updated_at" => "2024-09-16 13:03:24"
  ],
    [
    "key" => "CNG Premium",
    "created_at" => "2024-09-16 13:03:58",
    "updated_at" => "2024-09-16 13:03:58"
  ],
    [
    "key" => "CPA",
    "created_at" => "2024-09-16 13:05:02",
    "updated_at" => "2024-09-16 13:05:02"
  ],
    [
    "key" => "Pa To Owner Driver",
    "created_at" => "2024-09-16 13:05:52",
    "updated_at" => "2024-09-16 13:05:52"
  ],
    [
    "key" => "Idv Vehicle",
    "created_at" => "2024-09-16 13:06:40",
    "updated_at" => "2024-09-16 13:06:40"
  ],
    [
    "key" => "IDV Total",
    "created_at" => "2024-09-16 13:08:29",
    "updated_at" => "2024-09-16 13:08:29"
  ],
    [
    "key" => "Electrical Accessories Premium",
    "created_at" => "2024-09-16 13:13:53",
    "updated_at" => "2024-09-16 13:13:53"
  ],
    [
    "key" => "Nonelectrical Accessories Premium",
    "created_at" => "2024-09-17 07:39:26",
    "updated_at" => "2024-09-17 07:39:26"
  ],
    [
    "key" => "Zero Dep Premium",
    "created_at" => "2024-09-17 07:40:05",
    "updated_at" => "2024-09-17 07:40:05"
  ],
    [
    "key" => "Ll Paid Driver Premium",
    "created_at" => "2024-09-17 07:40:35",
    "updated_at" => "2024-09-17 07:40:35"
  ],
    [
    "key" => "Zd Previous Policy Addon",
    "created_at" => "2024-09-17 07:41:06",
    "updated_at" => "2024-09-17 07:41:06"
  ],
    [
    "key" => "Basic Od Premium",
    "created_at" => "2024-09-17 07:41:34",
    "updated_at" => "2024-09-17 07:41:34"
  ],
    [
    "key" => "Basic Tp Premium",
    "created_at" => "2024-09-17 07:41:57",
    "updated_at" => "2024-09-17 07:41:57"
  ],
    [
    "key" => "Payment Mode",
    "created_at" => "2024-09-17 07:42:39",
    "updated_at" => "2024-09-17 07:42:39"
  ],
    [
    "key" => "Premium Breakup",
    "created_at" => "2024-09-17 07:43:15",
    "updated_at" => "2024-09-17 07:43:15"
  ],
    [
    "key" => "Premium Breakup",
    "created_at" => "2024-09-17 07:45:19",
    "updated_at" => "2024-09-17 07:45:19"
  ]
        ]);
    }
}
