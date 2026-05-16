<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\File;

class CompanyMasterSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $path = storage_path('app/SqlFile/master_companies.sql');
        if (File::exists($path)) {
            $sql = File::get($path);

            DB::unprepared($sql);

            $this->command->info('SQL file executed successfully!');
        } else {
            $this->command->error('SQL file not found at: ' . $path);
        }
    }
}
