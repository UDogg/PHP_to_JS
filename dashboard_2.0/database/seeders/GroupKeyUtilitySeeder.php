<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Schema;

class GroupKeyUtilitySeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        if(Schema::hasTable('key_utility_report')) {
            DB::table('key_utility_report')->insert([

                    [
                        "key_utility_report_id" => 1,
                        "key" => "Personal Details",
                        "key_utility_id" => "2",
                        "created_at" => "2024-09-16 11:24:41",
                        "updated_at" => "2024-09-16 11:24:41",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 2,
                        "key" => "Personal Details",
                        "key_utility_id" => "3",
                        "created_at" => "2024-09-16 11:24:41",
                        "updated_at" => "2024-09-16 11:24:41",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 3,
                        "key" => "Personal Details",
                        "key_utility_id" => "4",
                        "created_at" => "2024-09-16 11:24:41",
                        "updated_at" => "2024-09-16 11:24:41",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 4,
                        "key" => "Personal Details",
                        "key_utility_id" => "5",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-25 10:18:27",
                        "deleted_at" => "2024-09-25 10:18:27"
                    ],
                    [
                        "key_utility_report_id" => 5,
                        "key" => "Personal Details",
                        "key_utility_id" => "6",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 6,
                        "key" => "Personal Details",
                        "key_utility_id" => "7",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 7,
                        "key" => "Personal Details",
                        "key_utility_id" => "8",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 8,
                        "key" => "Personal Details",
                        "key_utility_id" => "9",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 9,
                        "key" => "Personal Details",
                        "key_utility_id" => "10",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 10,
                        "key" => "Personal Details",
                        "key_utility_id" => "11",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 11,
                        "key" => "Personal Details",
                        "key_utility_id" => "12",
                        "created_at" => "2024-09-16 11:24:42",
                        "updated_at" => "2024-09-16 11:24:42",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 12,
                        "key" => "Nominee Details",
                        "key_utility_id" => "13",
                        "created_at" => "2024-09-16 11:25:28",
                        "updated_at" => "2024-09-16 11:25:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 13,
                        "key" => "Nominee Details",
                        "key_utility_id" => "14",
                        "created_at" => "2024-09-16 11:25:28",
                        "updated_at" => "2024-09-16 11:25:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 14,
                        "key" => "Nominee Details",
                        "key_utility_id" => "15",
                        "created_at" => "2024-09-16 11:25:28",
                        "updated_at" => "2024-09-16 11:25:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 15,
                        "key" => "Nominee Details",
                        "key_utility_id" => "16",
                        "created_at" => "2024-09-16 11:25:28",
                        "updated_at" => "2024-09-16 11:25:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 16,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "17",
                        "created_at" => "2024-09-16 11:26:43",
                        "updated_at" => "2024-09-16 11:26:43",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 17,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "18",
                        "created_at" => "2024-09-16 11:26:43",
                        "updated_at" => "2024-09-16 11:26:43",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 18,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "19",
                        "created_at" => "2024-09-16 11:26:43",
                        "updated_at" => "2024-09-16 11:26:43",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 19,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "20",
                        "created_at" => "2024-09-16 11:26:43",
                        "updated_at" => "2024-09-16 11:26:43",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 20,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "21",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 21,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "22",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 22,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "23",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 23,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "25",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 24,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "28",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 25,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "29",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 26,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "30",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 27,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "32",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 28,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "34",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 29,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "35",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 30,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "36",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 31,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "37",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 32,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "38",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 33,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "39",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 34,
                        "key" => "Vehicle Details",
                        "key_utility_id" => "40",
                        "created_at" => "2024-09-16 11:26:44",
                        "updated_at" => "2024-09-16 11:26:44",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 35,
                        "key" => "Others",
                        "key_utility_id" => "41",
                        "created_at" => "2024-09-21 14:02:31",
                        "updated_at" => "2024-09-21 14:02:31",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 36,
                        "key" => "Others",
                        "key_utility_id" => "42",
                        "created_at" => "2024-09-21 14:02:31",
                        "updated_at" => "2024-09-21 14:02:31",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 37,
                        "key" => "Others",
                        "key_utility_id" => "43",
                        "created_at" => "2024-09-21 14:02:31",
                        "updated_at" => "2024-09-21 14:02:31",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 38,
                        "key" => "Main",
                        "key_utility_id" => "44",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 39,
                        "key" => "Main",
                        "key_utility_id" => "45",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 40,
                        "key" => "Main",
                        "key_utility_id" => "46",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 41,
                        "key" => "Main",
                        "key_utility_id" => "47",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 42,
                        "key" => "Main",
                        "key_utility_id" => "48",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 43,
                        "key" => "Main",
                        "key_utility_id" => "49",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 44,
                        "key" => "Main",
                        "key_utility_id" => "50",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 45,
                        "key" => "Main",
                        "key_utility_id" => "51",
                        "created_at" => "2024-09-21 14:03:57",
                        "updated_at" => "2024-09-21 14:03:57",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 46,
                        "key" => "Main",
                        "key_utility_id" => "52",
                        "created_at" => "2024-09-21 14:03:58",
                        "updated_at" => "2024-09-21 14:03:58",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 47,
                        "key" => "Main",
                        "key_utility_id" => "53",
                        "created_at" => "2024-09-21 14:03:58",
                        "updated_at" => "2024-09-21 14:03:58",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 48,
                        "key" => "Main",
                        "key_utility_id" => "54",
                        "created_at" => "2024-09-21 14:03:58",
                        "updated_at" => "2024-09-21 14:03:58",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 49,
                        "key" => "Agent Details",
                        "key_utility_id" => "57",
                        "created_at" => "2024-09-21 14:07:37",
                        "updated_at" => "2024-09-21 14:07:37",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 50,
                        "key" => "Previous policy details",
                        "key_utility_id" => "68",
                        "created_at" => "2024-09-21 14:08:47",
                        "updated_at" => "2024-09-21 14:08:47",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 51,
                        "key" => "Previous policy details",
                        "key_utility_id" => "69",
                        "created_at" => "2024-09-21 14:08:47",
                        "updated_at" => "2024-09-21 14:08:47",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 52,
                        "key" => "Previous policy details",
                        "key_utility_id" => "70",
                        "created_at" => "2024-09-21 14:08:47",
                        "updated_at" => "2024-09-21 14:08:47",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 53,
                        "key" => "Previous policy details",
                        "key_utility_id" => "71",
                        "created_at" => "2024-09-21 14:08:47",
                        "updated_at" => "2024-09-21 14:08:47",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 54,
                        "key" => "Previous policy details",
                        "key_utility_id" => "72",
                        "created_at" => "2024-09-21 14:08:47",
                        "updated_at" => "2024-09-21 14:08:47",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 55,
                        "key" => "Current policy details",
                        "key_utility_id" => "74",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 56,
                        "key" => "Current policy details",
                        "key_utility_id" => "75",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 57,
                        "key" => "Current policy details",
                        "key_utility_id" => "76",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 58,
                        "key" => "Current policy details",
                        "key_utility_id" => "77",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 59,
                        "key" => "Current policy details",
                        "key_utility_id" => "79",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 60,
                        "key" => "Current policy details",
                        "key_utility_id" => "80",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 61,
                        "key" => "Current policy details",
                        "key_utility_id" => "81",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 62,
                        "key" => "Current policy details",
                        "key_utility_id" => "83",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 63,
                        "key" => "Current policy details",
                        "key_utility_id" => "84",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 64,
                        "key" => "Current policy details",
                        "key_utility_id" => "85",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 65,
                        "key" => "Current policy details",
                        "key_utility_id" => "86",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 66,
                        "key" => "Current policy details",
                        "key_utility_id" => "87",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 67,
                        "key" => "Current policy details",
                        "key_utility_id" => "88",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 68,
                        "key" => "Current policy details",
                        "key_utility_id" => "89",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 69,
                        "key" => "Current policy details",
                        "key_utility_id" => "90",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 70,
                        "key" => "Current policy details",
                        "key_utility_id" => "91",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 71,
                        "key" => "Current policy details",
                        "key_utility_id" => "92",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 72,
                        "key" => "Current policy details",
                        "key_utility_id" => "93",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 73,
                        "key" => "Current policy details",
                        "key_utility_id" => "94",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 74,
                        "key" => "Current policy details",
                        "key_utility_id" => "95",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 75,
                        "key" => "Current policy details",
                        "key_utility_id" => "96",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 76,
                        "key" => "Current policy details",
                        "key_utility_id" => "97",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 77,
                        "key" => "Current policy details",
                        "key_utility_id" => "111",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 78,
                        "key" => "Current policy details",
                        "key_utility_id" => "112",
                        "created_at" => "2024-09-21 14:28:28",
                        "updated_at" => "2024-09-21 14:28:28",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 79,
                        "key" => "Current policy details",
                        "key_utility_id" => "114",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 80,
                        "key" => "Current policy details",
                        "key_utility_id" => "115",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 81,
                        "key" => "Current policy details",
                        "key_utility_id" => "116",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 82,
                        "key" => "Current policy details",
                        "key_utility_id" => "117",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 83,
                        "key" => "Current policy details",
                        "key_utility_id" => "118",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 84,
                        "key" => "Current policy details",
                        "key_utility_id" => "119",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 85,
                        "key" => "Current policy details",
                        "key_utility_id" => "120",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 86,
                        "key" => "Current policy details",
                        "key_utility_id" => "121",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 87,
                        "key" => "Current policy details",
                        "key_utility_id" => "122",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 88,
                        "key" => "Current policy details",
                        "key_utility_id" => "123",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 89,
                        "key" => "Current policy details",
                        "key_utility_id" => "124",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 90,
                        "key" => "Current policy details",
                        "key_utility_id" => "126",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 91,
                        "key" => "Current policy details",
                        "key_utility_id" => "127",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 92,
                        "key" => "Current policy details",
                        "key_utility_id" => "128",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 93,
                        "key" => "Current policy details",
                        "key_utility_id" => "129",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 94,
                        "key" => "Current policy details",
                        "key_utility_id" => "131",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 95,
                        "key" => "Current policy details",
                        "key_utility_id" => "132",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 96,
                        "key" => "Current policy details",
                        "key_utility_id" => "133",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 97,
                        "key" => "Current policy details",
                        "key_utility_id" => "134",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 98,
                        "key" => "Current policy details",
                        "key_utility_id" => "135",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 99,
                        "key" => "Current policy details",
                        "key_utility_id" => "136",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 100,
                        "key" => "Current policy details",
                        "key_utility_id" => "137",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 101,
                        "key" => "Current policy details",
                        "key_utility_id" => "138",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 102,
                        "key" => "Current policy details",
                        "key_utility_id" => "139",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 103,
                        "key" => "Current policy details",
                        "key_utility_id" => "140",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 104,
                        "key" => "Current policy details",
                        "key_utility_id" => "141",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 105,
                        "key" => "Current policy details",
                        "key_utility_id" => "142",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 106,
                        "key" => "Current policy details",
                        "key_utility_id" => "143",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 107,
                        "key" => "Current policy details",
                        "key_utility_id" => "144",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 108,
                        "key" => "Current policy details",
                        "key_utility_id" => "145",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 109,
                        "key" => "Current policy details",
                        "key_utility_id" => "146",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 110,
                        "key" => "Current policy details",
                        "key_utility_id" => "147",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 111,
                        "key" => "Current policy details",
                        "key_utility_id" => "149",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 112,
                        "key" => "Current policy details",
                        "key_utility_id" => "150",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 113,
                        "key" => "Current policy details",
                        "key_utility_id" => "151",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 114,
                        "key" => "Current policy details",
                        "key_utility_id" => "152",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 115,
                        "key" => "Current policy details",
                        "key_utility_id" => "153",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 116,
                        "key" => "Current policy details",
                        "key_utility_id" => "154",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 117,
                        "key" => "Current policy details",
                        "key_utility_id" => "155",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 118,
                        "key" => "Current policy details",
                        "key_utility_id" => "156",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 119,
                        "key" => "Current policy details",
                        "key_utility_id" => "157",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 120,
                        "key" => "Current policy details",
                        "key_utility_id" => "158",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ],
                    [
                        "key_utility_report_id" => 121,
                        "key" => "Current policy details",
                        "key_utility_id" => "159",
                        "created_at" => "2024-09-21 14:28:29",
                        "updated_at" => "2024-09-21 14:28:29",
                        "deleted_at" => null
                    ]

            ]);

        }
    }
}
