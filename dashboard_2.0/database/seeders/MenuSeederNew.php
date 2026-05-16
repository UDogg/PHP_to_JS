<?php

namespace Database\Seeders;

use App\Models\MenuMasterModel;
use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;

class MenuSeederNew extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $insertMainMenu = MenuMasterModel::insert([
            [
                'menu' => 'Dashboard',
                'icon' => 'MdSpaceDashboard',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'dashboard'
            ],
            [
                'menu' => 'Policy Management',
                'icon' => '',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => ''
            ],
            [
                'menu' => 'User Onboarding',
                'icon' => '',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => ''
            ],
            [
                'menu' => 'User Access Control',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => '',
                'icon' => 'FaUserGear'

            ],
            [
                'menu' => 'MIS Reports',
                'icon' => 'RiStackFill',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => ''
            ],

            [
                'menu' => 'User Management',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => '',
                'icon' => '',
            ],
            [
                'menu' => 'Commission Utility',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'xyz'
            ],
            [
                'menu' => 'Logs Management',
                'icon' => 'RiStackFill',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => ''
            ],
            [
                'menu' => 'Settings',
                'icon' => 'RiStackFill',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => ''
            ],
            [
                'menu' => 'Sell Now',
                'icon' => 'SiSellfy',
                'is_child' => 'N',
                'isFrontEnd' => 'N',
                'front_end_url' => 'sell-now'
            ],


        ]);

        $MasterId = MenuMasterModel::where('menu', 'Policy Management')->first();

        $insertMasters = MenuMasterModel::insert([
            [
                'menu' => 'Renewal',
                'menuId' => $MasterId->id,
                // 'route' => 'user.index',
                //                'MenuPermissionName' => 'user.view',
                'front_end_url' => 'renewal-policy',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Offline Excel Keys',
                'menuId' => $MasterId->id,
                'front_end_url' => 'excel-creation',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Offline Excel Configurator',
                'menuId' => $MasterId->id,
                'front_end_url' => 'excel-edit',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Offline Policy Upload',
                'menuId' => $MasterId->id,
                'front_end_url' => 'offline-policy-upload',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Policy Status',
                'menuId' => $MasterId->id,
                // 'route' => 'policystatus',
                'front_end_url' => 'PolicyStatusReport',
                'isFrontEnd' => 'Y',
                // 'route' => 'policystatus',
            ],

        ]);

        $UACID = MenuMasterModel::where('menu', 'User Access Control')->first();
        $insertUAC = MenuMasterModel::insert([
            [
                'menu' => 'Roles Master',
                'menuId' => $UACID->id,
                'route' => 'roles.index',
                'front_end_url' => 'Roles',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'AccessControl',
                'menuId' => $UACID->id,
                'route' => 'AccessControlView',
                'front_end_url' => 'AccessControl',
                'isFrontEnd' => 'Y'
            ],
        ]);

        $userOnboardingId = MenuMasterModel::where('menu', 'User Onboarding')->first();
        $uo = MenuMasterModel::insert([
            [
                'menu' => 'User Creation',
                'menuId' => $userOnboardingId->id,
                'front_end_url' => 'newUsers',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'OEM Onboarding',
                'menuId' => $userOnboardingId->id,
                'front_end_url' => 'oem',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'MISP Onboarding',
                'menuId' => $userOnboardingId->id,
                'front_end_url' => 'misp-onboarding',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Branch Onboarding',
                'menuId' => $userOnboardingId->id,
                'front_end_url' => 'branch',
                'isFrontEnd' => 'Y'
            ],
        ]);

        $misReportID = MenuMasterModel::where('menu', 'MIS Reports')->first();
        $mr = MenuMasterModel::insert([
            [
                'menu' => 'Report Scheduler',
                'menuId' => $misReportID->id,
                'front_end_url' => 'report-scheduler',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Report',
                'menuId' => $misReportID->id,
                'front_end_url' => 'reports',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'MIS Configurator',
                'menuId' => $misReportID->id,
                'front_end_url' => 'report-configurator',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Report Template List',
                'menuId' => $misReportID->id,
                'front_end_url' => 'template-list',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Downloaded Reports',
                'menuId' => $misReportID->id,
                'front_end_url' => 'download-reports',
                'isFrontEnd' => 'Y'
            ]
        ]);

        $userManagement = MenuMasterModel::where('menu', 'User Management')->first();
        $um = MenuMasterModel::insert([
            [
                'menu' => 'Delegate',
                'menuId' => $userManagement->id,
                'front_end_url' => 'delegates',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Corporate Onboarding',
                'menuId' => $userManagement->id,
                'front_end_url' => 'onboard',
                'isFrontEnd' => 'Y'
            ]
        ]);


        $logsManagement = MenuMasterModel::where('menu', 'Logs Management')->first();
        $lm = MenuMasterModel::insert([
            [
                'menu' => 'Visibility Report',
                'menuId' => $logsManagement->id,
                'front_end_url' => 'visibility-report',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Change Log',
                'menuId' => $logsManagement->id,
                'front_end_url' => 'activity-log',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Login History',
                'menuId' => $logsManagement->id,
                'front_end_url' => 'login-count',
                'isFrontEnd' => 'Y'
            ]

        ]);

        $settingsID = MenuMasterModel::where('menu', 'Settings')->first();
        $set = MenuMasterModel::insert([
            [
                'menu' => 'Create FAQ',
                'menuId' => $settingsID->id,
                'front_end_url' => 'admin-faq',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Theme Configurator',
                'menuId' => $settingsID->id,
                'front_end_url' => 'theme',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'POS ic mapping',
                'menuId' => $settingsID->id,
                'front_end_url' => 'pos-mapping',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Profile',
                'menuId' => $settingsID->id,
                'front_end_url' => 'profile',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Broker Details',
                'menuId' => $settingsID->id,
                'front_end_url' => 'broker-details',
                'isFrontEnd' => 'Y'
            ]
        ]);

        $masterBackend = MenuMasterModel::insert([
            [
                'menu' => 'Masters',
                'icon' => 'RiStackFill',
                'is_child' => 'Y',
                'isFrontEnd' => 'N',
                'front_end_url' => null
            ],
        ]);
         
        $MasterIdBcakend = MenuMasterModel::where('menu', 'Masters')->first();

        $insertMasters = MenuMasterModel::insert([
            [
                'menu' => 'Users',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'user.index',
//                'MenuPermissionName' => 'user.view',
                'front_end_url' => 'User',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Credentials',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'credential.index',
//                'MenuPermissionName' => 'credential.view',
                'front_end_url' => 'Credential',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Brokers',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'broker.index',
//                'MenuPermissionName' => 'broker.view',
                'front_end_url' => 'Broker',
                'isFrontEnd' => 'N'

            ],
            [
                'menu' => 'Sessions',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'session.index',
//                'MenuPermissionName' => 'session.view',
                'front_end_url' => 'Session',
                'isFrontEnd' => 'N'

            ],
            [
                'menu' => 'OTP',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'otp.index',
//                'MenuPermissionName' => 'otp.view',
                'front_end_url' => 'Otp',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Placeholders',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'placeholder.index',
//                'MenuPermissionName' => 'placeholder.view',
                'front_end_url' => 'Placeholder',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'SMS Templates',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'sms_template.index',
//                'MenuPermissionName' => 'sms_template.view',
                'front_end_url' => 'SmsTemplate',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Events',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'event.index',
//                'MenuPermissionName' => 'event.view',
                'front_end_url' => 'Event',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Templates',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'template.index',
//                'MenuPermissionName' => 'template.view',
                'front_end_url' => 'Template',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Stage Master',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'stagemaster.index',
//                'MenuPermissionName' => 'stagemaster.view',
                'front_end_url' => 'Stagemaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Lobs',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'lob',
//                'MenuPermissionName' => 'lob.view',
                'front_end_url' => 'Lob',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Key Utility',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'KeyUtility.index',
//                'MenuPermissionName' => 'keyutility.view',
                'front_end_url' => 'KeyUtility',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Group Key Utility',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'reportKeyUtility.index',
//                'MenuPermissionName' => 'groupKeyUtility.view',
                'front_end_url' => 'GroupKeyUtility',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Zones',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'zone_master',
//                'MenuPermissionName' => 'ZoneMaster.view',
                'front_end_url' => 'ZoneMaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Policy Status Column Master',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'policystatus_column_master',
//                'MenuPermissionName' => 'policystatus.view',
                'front_end_url' => '',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'CTA Master',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'cta_master',
//                'MenuPermissionName' => 'cta.view',
                'front_end_url' => 'CtaMaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Policy Report Filter Master',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'PolicyStatusFilterMaster.index',
//                'MenuPermissionName' => 'policyStatusFilterMaster.view',
                'front_end_url' => '',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Qualification Master',
                'menuId' => $MasterIdBcakend->id,
                'route' => 'qualification',
//                'MenuPermissionName' => 'policyStatusFilterMaster.view',
                'front_end_url' => '',
                'isFrontEnd' => 'N'
            ],


        ]);

        $UACID_BACKEND = MenuMasterModel::where('menu', 'User Access Control')->first();
        $insertUAC = MenuMasterModel::insert([
            [
                'menu' => 'User Type Master',
                'menuId' => $UACID_BACKEND->id,
                'route' => 'UserTypes.index',
//                'MenuPermissionName' => 'usertype.view',
                'front_end_url' => 'UserTypes',
                'isFrontEnd' => 'N'
            ] ,
            [
                'menu' => 'Menu Master',
                'menuId' => $UACID_BACKEND->id,
                'route' => 'MenuMaster',
//                'MenuPermissionName' => 'menu.view',
                'front_end_url' => 'MenuMaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Config Permission Mapping',
                'menuId' => $UACID_BACKEND->id,
                'route' => 'PermissionView',
//                'MenuPermissionName' => 'ConfigPermission.view',
                'front_end_url' => 'ConfigPermission',
                'isFrontEnd' => 'N'
            ]
        ]);

    }
}
