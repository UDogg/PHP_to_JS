<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\File;

class PincodeSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $path = storage_path('app/SqlFile/pincode_master.sql');

        if (File::exists($path)) {
            $sql = File::get($path);

            try {
                DB::unprepared($sql);
                $this->command->info('SQL file executed successfully!');
            } catch (\Exception $e) {
                $this->command->error('Error inserting data: ' . $e->getMessage());
            }
        } else {
            $this->command->error('SQL file not found at: ' . $path);
        }
    }
}
