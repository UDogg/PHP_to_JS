<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class ChannelMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('channel_master')->insert([
            [
                'channel_name' => 'LA- Premier',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'channel_name' => 'Branches',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'channel_name' => 'HO-SUPPORT ',
                'created_at' => now(),
                'updated_at' => now(),
            ],
            [
                'channel_name' => 'Other Channels',
                'created_at' => now(),
                'updated_at' => now(),
            ]
        ]);
    }
}
