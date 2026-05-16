<?php

namespace Database\Seeders;

use App\Models\User;
// use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class DatabaseSeeder extends Seeder
{
    /**
     * Seed the application's database.
     */
    public function run(): void
    {
        // DB::disableQueryLog(); // Add this line

        DB::beginTransaction();
            try {

            $this->call([
                BrokerSeeder::class,
                lob_master_seeder::class,
                StageSeeder::class,
                SubStageSeeder::class,
                FilterMasterSeeder::class,
                PolicyStatusColumnMasterSeeder::class,
                KeyUtilitySeeder::class,
                ketUtilityMappings::class,
                UsertypeSeeder::class,
                PincodeSeeder::class,
                CitySeeder::class,
                StateSeeder::class,
                ExcelKeymaster::class,
                PolicyStatusColumnMasterSeeder::class,
                ClaimMasterSeeder::class,
                rolesSeeder::class,
                // MenuSeeder::class,
                MenuSeederNew::class,
                permissionsSeeder::class,
                QualificationSeeder::class,
                UsersTableSeeder::class,
                UsertypeAdminUserSeeder::class,
                PosAdminUserSeeder::class,
                PartnerAdminUserSeeder::class,
                // IFSCcodeSeeder::class,
                GroupKeyUtilitySeeder::class,
                ZoneMasterSeeder::class,
                ConfigSettingsSeeder::class,
                LoginhistorySeeder::class,
                CtaMasterSeeder::class,
                UserAccessManagementSeeder::class,
                // CompanyMasterSeeder::class,
                DashboardTablesSeeder::class,
                CompanySeeder::class,

                VehicleTypeSeeder::class,
                VehicleSubTypeSeeder::class,
                

                FuelTypeSeeder::class,
                BusinessTypeSeeder::class,
                VehicleTypeRangesSeeder::class,
                ChannelMasterSeeder::class,
                BranchMasterSeeder::class,

                MaskingTypeSeeder::class
            ]);
                DB::commit();
            }
            catch (\Exception $e) {
                DB::rollBack();
                throw $e;
            }

    }
}
