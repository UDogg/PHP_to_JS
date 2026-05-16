<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class LoginhistorySeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        DB::table('login_history')->insert([
            [
                'user_id' => 1,
                'ip' => '127.0.0.1',
                'browser' => 'Chrome',
                'created_at' => now(),
            ],
            [
                'user_id' => 2,
                'ip' => '127.0.0.1',
                'browser' => 'Chrome',
                'created_at' => now(),
            ],
            [
                'user_id' => 3,
                'ip' => '127.0.0.1',
                'browser' => 'Chrome',
                'created_at' => now(),
            ],
            [
                'user_id' => 4,
                'ip' => '127.0.0.1',
                'browser' => 'Chrome',
                'created_at' => now(),
            ],
            ]);
    }
}
