<?php

namespace Database\Seeders;

use Carbon\Carbon;
use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Schema;

class UserAccessManagementSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
    if(Schema::hasTable('menumaster')) {
        $menuId = DB::table('menumaster')->where('menu','User Creation')->pluck('id')->first();

        $userTypeCollection = DB::table('usertypes')->where('is_active','Y')->pluck('Identifier');

        $identifier = $userTypeCollection->toArray();

        $data = json_encode([
            'manage_access' => [
                [
                    'menu_id' => $menuId,
                    'identifier' => $identifier,
                    'allowedUserCreation' => $identifier
                ]
            ]
        ]);

        $array = [
            'role_id' => 2,
            'user_id' => 2,
            'data' => $data,
            'type' => 'E',
            'status' => 'Y',
            'created_at' => Carbon::now('Asia/Kolkata')->format('Y-m-d H:i:s'),
            'updated_at' => Carbon::now('Asia/Kolkata')->format('Y-m-d H:i:s')
           
        ];

        $arraytwo = [
           'role_id' => 1,
            'user_id' => 1,
            'data' => $data,
            'type' => 'E',
            'status' => 'Y',
            'created_at' => Carbon::now('Asia/Kolkata')->format('Y-m-d H:i:s'),
            'updated_at' => Carbon::now('Asia/Kolkata')->format('Y-m-d H:i:s')
        ];


        DB::table('user_access_managment')->insert($arraytwo);
        DB::table('user_access_managment')->insert($array);
    }

    }
}
