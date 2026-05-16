<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\File;

class IFSCcodeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        $path = storage_path('app/SqlFile/ifsc_master.sql');
        if (File::exists($path)) {
            // Read the contents of the SQL file
            $sql = File::get($path);

            // Execute the SQL commands
            DB::unprepared($sql);

            $this->command->info('SQL file executed successfully!');
        } else {
            $this->command->error('SQL file not found at: ' . $path);
        }
    }
}
