<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class DashboardTablesSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        DB::table('ic_master')->insert([
            ['id' => 1, 'ic_id' => 3, 'ic_name' => 'Bajaj Allianz GIC'],
            ['id' => 2, 'ic_id' => 5, 'ic_name' => 'LandT Insurance'],
            ['id' => 3, 'ic_id' => 7, 'ic_name' => 'Cigna TTK Insurance'],
            ['id' => 4, 'ic_id' => 11, 'ic_name' => 'HDFC ERGO General Insurance'],
            ['id' => 5, 'ic_id' => 13, 'ic_name' => 'IFFCO Tokio General Insurance Co. Ltd.'],
            ['id' => 6, 'ic_id' => 16, 'ic_name' => 'New India Assurance'],
            ['id' => 7, 'ic_id' => 20, 'ic_name' => 'Reliance General Insurance'],
            ['id' => 8, 'ic_id' => 22, 'ic_name' => 'Tata AIG General Insurance'],
            ['id' => 9, 'ic_id' => 25, 'ic_name' => 'United India Insurance'],
            ['id' => 10, 'ic_id' => 29, 'ic_name' => 'Bharti AXA General Insurance'],
            ['id' => 11, 'ic_id' => 30, 'ic_name' => 'Future Generali General Insurance'],
            ['id' => 12, 'ic_id' => 31, 'ic_name' => 'Universal Sompo General Insurance'],
            ['id' => 13, 'ic_id' => 32, 'ic_name' => 'Chola MS General Insurance'],
            ['id' => 14, 'ic_id' => 33, 'ic_name' => 'Liberty General Insurance'],
            ['id' => 15, 'ic_id' => 34, 'ic_name' => 'Shriram General Insurance Co. Ltd.'],
            ['id' => 16, 'ic_id' => 35, 'ic_name' => 'SBI General Insurance Company Limited'],
            ['id' => 17, 'ic_id' => 36, 'ic_name' => 'Royal Sundaram General Insurance Co. Limited'],
            ['id' => 18, 'ic_id' => 37, 'ic_name' => 'Go Digit General Insurance Ltd.'],
            ['id' => 19, 'ic_id' => 39, 'ic_name' => 'Kotak Mahindra General'],
            ['id' => 20, 'ic_id' => 40, 'ic_name' => 'Acko General Insurance Ltd.'],
            ['id' => 21, 'ic_id' => 41, 'ic_name' => 'ICICI Lombard General Insurance Co. Ltd.'],
            ['id' => 22, 'ic_id' => 42, 'ic_name' => 'Magma HDI General Insurance Co. Ltd.'],
            ['id' => 23, 'ic_id' => 43, 'ic_name' => 'Raheja QBE General Insurance Company Limited'],
            ['id' => 24, 'ic_id' => 44, 'ic_name' => 'Zuno General Insurance Limited'],
            ['id' => 25, 'ic_id' => 45, 'ic_name' => 'Oriental General Insurance'],
            ['id' => 26, 'ic_id' => 46, 'ic_name' => 'National Insurance Co. Ltd.'],
        ]);

        DB::table('policy_category')->insert([
            ['id' => 1, 'category_id' => 1, 'category_name' => 'CAR'],
            ['id' => 2, 'category_id' => 2, 'category_name' => 'BIKE'],
            ['id' => 3, 'category_id' => 3, 'category_name' => 'MISC'],
            ['id' => 4, 'category_id' => 17, 'category_name' => 'AGRICULTURAL-TRACTOR'],
            ['id' => 5, 'category_id' => 18, 'category_name' => 'MISCELLANEOUS-CLASS'],
            ['id' => 6, 'category_id' => 4, 'category_name' => 'GCV'],
            ['id' => 7, 'category_id' => 9, 'category_name' => 'PICK UP/DELIVERY/REFRIGERATED VAN'],
            ['id' => 8, 'category_id' => 13, 'category_name' => 'DUMPER/TIPPER'],
            ['id' => 9, 'category_id' => 14, 'category_name' => 'TRUCK'],
            ['id' => 10, 'category_id' => 15, 'category_name' => 'TRACTOR'],
            ['id' => 11, 'category_id' => 16, 'category_name' => 'TANKER/BULKER'],
            ['id' => 12, 'category_id' => 8, 'category_name' => 'PCV'],
            ['id' => 13, 'category_id' => 5, 'category_name' => 'AUTO-RICKSHAW'],
            ['id' => 14, 'category_id' => 6, 'category_name' => 'TAXI'],
            ['id' => 15, 'category_id' => 7, 'category_name' => 'PASSENGER-BUS'],
            ['id' => 16, 'category_id' => 10, 'category_name' => 'SCHOOL-BUS'],
            ['id' => 17, 'category_id' => 11, 'category_name' => 'ELECTRIC-RICKSHAW'],
            ['id' => 18, 'category_id' => 12, 'category_name' => 'TEMPO-TRAVELLER'],
        ]);

        DB::table('policy_type_master')->insert([
            ['id' => 1, 'type_id' => 1, 'policy_type_name' => 'comprehensive'],
            ['id' => 2, 'type_id' => 2, 'policy_type_name' => 'third_party'],
            ['id' => 3, 'type_id' => 3, 'policy_type_name' => 'own_damage'],
            ['id' => 4, 'type_id' => 4, 'policy_type_name' => 'breakin'],
            ['id' => 5, 'type_id' => 5, 'policy_type_name' => 'Short Term 3 months'],
            ['id' => 6, 'type_id' => 6, 'policy_type_name' => 'Own Damage Breakin'],
            ['id' => 7, 'type_id' => 7, 'policy_type_name' => 'Third Party Breakin'],
            ['id' => 8, 'type_id' => 8, 'policy_type_name' => 'Short Term 6 months'],
        ]);
    }
}
