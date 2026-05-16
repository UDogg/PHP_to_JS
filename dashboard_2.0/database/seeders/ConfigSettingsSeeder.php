<?php

namespace Database\Seeders;

use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class ConfigSettingsSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
        $configGroupId = DB::table('ConfigMaster')->insertGetId([
           'key' => 'mongoDB',
           'created_at' => now()
        ]);
        $configMasterID = $configGroupId;


        DB::table('config_settings')->insert([
            [
                'credential_label' => 'DB_MONGO_HOST',
                'credential_key' => 'database.connections.mongodb.host',
                'credential_value' => credential_encrypt('13.235.92.4'),
                'configuration' => $configMasterID,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'DB_MONGO_PORT',
                'credential_key' => 'database.connections.mongodb.port',
                'credential_value' => credential_encrypt('27017'),
                'configuration' => $configMasterID,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'DB_MONGO_DATABASE',
                'credential_key' => 'database.connections.mongodb.database',
                'credential_value' => credential_encrypt('fyntune_health'),
                'configuration' => $configMasterID,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'DB_MONGO_USERNAME',
                'credential_key' => 'database.connections.mongodb.username',
                'credential_value' => credential_encrypt('fyntune_dbuser'),
                'configuration' => $configMasterID,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'DB_MONGO_PASSWORD',
                'credential_key' => 'database.connections.mongodb.password',
                'credential_value' => credential_encrypt('healthApi900#'),
                'configuration' => $configMasterID,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'DB_MONGO_AUTH_DATABASE',
                'credential_key' => 'database.connections.mongodb.options.database',
                'credential_value' => credential_encrypt('fyntune_health'),
                'configuration' => $configMasterID,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
        ]);
       $brokerConfigGroupId = DB::table('ConfigMaster')->insertGetId([
            'key' => 'BrokerConfigurations',
            'created_at' => now()
            ]);
        $blInsertId = $brokerConfigGroupId;
        DB::table('config_settings')->insert([
            [
                'credential_label' => 'SSO Username',
                'credential_key' => 'sso_user_name',
                'credential_value' => credential_encrypt('admin'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'SSO Password',
                'credential_key' => 'sso_passwprd',
                'credential_value' => credential_encrypt('admin'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'SSO Encrypt Key',
                'credential_key' => 'sso_encryption_key',
                'credential_value' => credential_encrypt('admin'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'broker froneend dashboard url',
                'credential_key' => 'Broker.FrontendUrl.dashboard',
                'credential_value' => credential_encrypt('https://uatdashboard-revamp.fynity.in/'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'broker term frontend url',
                'credential_key' => 'Broker.FrontendUrl.term',
                'credential_value' => credential_encrypt('https://demo-term.fynity.in/'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'broker investment backend url',
                'credential_key' => 'Broker.BackendUrl.investment',
                'credential_value' => credential_encrypt('https://demo-investment.fynity.in/'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'broker term backend url',
                'credential_key' => 'excel.data.limit.download',
                'credential_value' => credential_encrypt(2000),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'allow user of multiple usertype',
                'credential_key' => 'Broker.Allow.Multiple.users',
                'credential_value' => credential_encrypt('N'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'default create partner user',
                'credential_key' => 'Broker.Default.Partner',
                'credential_value' => credential_encrypt('N'),
                'configuration' => $blInsertId,
                'enviroment' => 'local',
                'created_at' => now(),
            ]

        ]);

        $lobapi  = DB::table('ConfigMaster')->insertGetId([
            'key' => "LOB-API",
            'created_at' => now()
        ]);
        $lobapiId=  $lobapi;
        DB::table('config_settings')->insert([
            [
                'credential_label' => 'Motor Visibility Deatils API	',
                'credential_key' => 'MotorVisibilityReportAPI',
                'credential_value' => credential_encrypt('https://uatpos.heroinsurance.com/api/generate_pos_token'),
                    'enviroment' => 'local',
                'created_at' => now()
            ]
        ]);
        $thirdpartyApiId = DB::table('config_settings')->insert([
            [
                'credential_label' => 'Motor Api',
                'credential_key' => 'motor-api',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/fetch-master'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'motor-Get-Segment-Api	',
                'credential_key' => 'motor-get-segment-api',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/get-segments'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Get ic by segment',
                'credential_key' => 'get-ic-by-segment',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/get-ic-by-segment'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Get Imd Mapping',
                'credential_key' => 'get-imd-mapping',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/get-imd-mapping'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Get MMV Mapping',
                'credential_key' => 'get-mmv-mapping',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/get-mmv-mapping'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Add MMV Utility',
                'credential_key' => 'add-mmv-utility',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/add-mmv-utility'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'RTO UTILITY',
                'credential_key' => 'rto-utility',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/add-rto-utility'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Get-Rto-Mapping',
                'credential_key' => 'get-rto-mapping',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/get-rto-mapping'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Add ic parameter posp utility',
                'credential_key' => 'add-ic-parameter-posp-utility',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/add-ic-parameter'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],
            [
                'credential_label' => 'Update Record Posp Utility',
                'credential_key' => 'update-record-posp-utility',
                'credential_value' => credential_encrypt('https://apiuatmotor.rbstaging.in/api/posp-utility/update-record'),
                'enviroment' => 'local',
                'created_at' => now(),
            ],


        ]);

    }
}
