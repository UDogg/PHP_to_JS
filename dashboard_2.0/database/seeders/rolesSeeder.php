<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;
use Spatie\Permission\Models\Role;

class rolesSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
//        DB::statement('alter table roles  AUTO_INCREMENT = 1');
        $default_role = Role::insert([
        [
            'name' => 'Super Admin',
            'guard_name' => 'sanctum',
            'user_type' => 0,
            'reporting_role' => 0
        ],
        [
            'name' => 'Employee Admin',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'E')->first()->id,
            'reporting_role' => 0
        ],
            [
            'name' => 'Employee',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'E')->first()->id,
            'reporting_role' => 2
        ],
        [
            'name' => 'Posp Admin',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'P')->first()->id,
            'reporting_role' => 0
        ],
            [
            'name' => 'Posp',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'P')->first()->id,
            'reporting_role' =>  4
        ],
        [
            'name' => 'Partner Admin',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'Partner')->first()->id,
            'reporting_role' => 0
        ],
        [
            'name' => 'Partner',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'Partner')->first()->id,
            'reporting_role' => 6
        ],
        [
        'name' => 'B2C Admin',
        'guard_name' => 'sanctum',
        'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'b2c')->first()->id,
        'reporting_role' => 0
        ],
        [
        'name' => 'Customer',
        'guard_name' => 'sanctum',
        'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'U')->first()->id,
        'reporting_role' => 8
        ],
        [
            'name' => 'Misp Admin',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'MISP')->first()->id,
            'reporting_role' => 0

        ],
        [
            'name' => 'SP Admin',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'SP')->first()->id,
            'reporting_role' => 0

        ],
        [
            'name' => 'SP',
            'guard_name' => 'sanctum',
            'user_type' => DB::table('usertypes')->select('id')->where('Identifier', 'SP')->first()->id,
            'reporting_role' => 0

        ]
        ]);


    }
}
