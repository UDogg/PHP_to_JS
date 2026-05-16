<?php

namespace Database\Seeders;

use App\Models\MenuMasterModel;
use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class MenuSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        //
//        DB::statement('ALTER TABLE MenuMaster AUTO_INCREMENT = 1');
        $insertMainMenu = MenuMasterModel::insert([
            [
                'menu' => 'Masters',
                'icon' => 'RiStackFill',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => null
            ],
            [
                'menu' => 'User Access Control',
                'icon' => 'FaUserGear',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => null
            ],
            [
                'menu' => 'Logs',
                'icon' => 'GoLog',
                'is_child' => 'Y',
                'isFrontEnd' => 'Y',
                'front_end_url' => null

            ],
            [
                'menu' => 'Dashboard',
                'icon' => 'MdSpaceDashboard',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'dashboard'
            ],
            [
                'menu' => 'Sell Now',
                'icon' => 'SiSellfy',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'sell-now'
            ],
            [
                'menu' => 'Delegate',
                'icon' => 'GrUserAdmin',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'delegates'
            ],
            [
                'menu' => 'Login History',
                'icon' => 'FaHistory',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'login-count'
            ],
            [
                'menu' => 'Template List',
                'icon' => 'CiViewList',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'template-list'
            ],
            [
                'menu' => 'Offline Policy Upload',
                'icon' => 'MdPolicy',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'offline-policy-upload'
            ],
            [
                'menu' => 'profile',
                'icon' => 'GrDocumentConfig',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'profile'
            ],
            [
                'menu' => 'POS ic mapping',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'pos-mapping'
            ],
            [
                'menu' => 'Renewal',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'renewal-policy'
            ],
            [
                'menu' => 'MIS Configurator',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'report-configurator'
            ],
            [
                'menu' => 'MIS Reports',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'reports'
            ],
            [
                'menu' => 'FAQ?',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'faq'
            ],
            [
                'menu' => 'My Policies',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'my-policies'
            ],
            [
                'menu' => 'My Vehicle',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'my-vehicle'
            ],
            [
                'menu' => 'Corporate Onboarding',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'my-vehicle'
            ],
            [
                'menu' => 'Recent Search',
                'icon' => 'RiStackFill',
                'is_child' => 'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'search'
            ],
            [
                'menu' => 'Create FAQ',
                'icon' => 'RiStackFill',
                'is_child' =>    'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'admin-faq'
            ],
            [
                'menu' => 'Bulk Upload',
                'icon' => 'RiStackFill',
                'is_child' =>    'N',
                'isFrontEnd' => 'Y',
                'front_end_url' => 'bulk-upload'
            ]

        ]);
        $MasterId = MenuMasterModel::where('menu', 'Masters')->first();
        $insertMasters = MenuMasterModel::insert([
            [
                'menu' => 'Users',
                'menuId' => $MasterId->id,
                'route' => 'user.index',
//                'MenuPermissionName' => 'user.view',
                'front_end_url' => 'User',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Credentials',
                'menuId' => $MasterId->id,
                'route' => 'credential.index',
//                'MenuPermissionName' => 'credential.view',
                'front_end_url' => 'Credential',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Brokers',
                'menuId' => $MasterId->id,
                'route' => 'broker.index',
//                'MenuPermissionName' => 'broker.view',
                'front_end_url' => 'Broker',
                'isFrontEnd' => 'N'

            ],
            [
                'menu' => 'Sessions',
                'menuId' => $MasterId->id,
                'route' => 'session.index',
//                'MenuPermissionName' => 'session.view',
                'front_end_url' => 'Session',
                'isFrontEnd' => 'N'

            ],
            [
                'menu' => 'OTP',
                'menuId' => $MasterId->id,
                'route' => 'otp.index',
//                'MenuPermissionName' => 'otp.view',
                'front_end_url' => 'Otp',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Placeholders',
                'menuId' => $MasterId->id,
                'route' => 'placeholder.index',
//                'MenuPermissionName' => 'placeholder.view',
                'front_end_url' => 'Placeholder',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'SMS Templates',
                'menuId' => $MasterId->id,
                'route' => 'sms_template.index',
//                'MenuPermissionName' => 'sms_template.view',
                'front_end_url' => 'SmsTemplate',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Events',
                'menuId' => $MasterId->id,
                'route' => 'event.index',
//                'MenuPermissionName' => 'event.view',
                'front_end_url' => 'Event',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Templates',
                'menuId' => $MasterId->id,
                'route' => 'template.index',
//                'MenuPermissionName' => 'template.view',
                'front_end_url' => 'Template',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Stage Master',
                'menuId' => $MasterId->id,
                'route' => 'stagemaster.index',
//                'MenuPermissionName' => 'stagemaster.view',
                'front_end_url' => 'Stagemaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Lobs',
                'menuId' => $MasterId->id,
                'route' => 'lob',
//                'MenuPermissionName' => 'lob.view',
                'front_end_url' => 'Lob',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Key Utility',
                'menuId' => $MasterId->id,
                'route' => 'KeyUtility.index',
//                'MenuPermissionName' => 'keyutility.view',
                'front_end_url' => 'KeyUtility',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Group Key Utility',
                'menuId' => $MasterId->id,
                'route' => 'reportKeyUtility.index',
//                'MenuPermissionName' => 'groupKeyUtility.view',
                'front_end_url' => 'GroupKeyUtility',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Zones',
                'menuId' => $MasterId->id,
                'route' => 'zone_master',
//                'MenuPermissionName' => 'ZoneMaster.view',
                'front_end_url' => 'ZoneMaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Policy Status',
                'menuId' => null,
                'route' => 'policystatus',
//                'MenuPermissionName' => 'policystatus.view',
                'front_end_url' => 'PolicyStatusReport',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Policy Status Column Master',
                'menuId' => $MasterId->id,
                'route' => 'policystatus_column_master',
//                'MenuPermissionName' => 'policystatus.view',
                'front_end_url' => '',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'CTA Master',
                'menuId' => $MasterId->id,
                'route' => 'cta_master',
//                'MenuPermissionName' => 'cta.view',
                'front_end_url' => 'CtaMaster',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Policy Report Filter Master',
                'menuId' => $MasterId->id,
                'route' => 'PolicyStatusFilterMaster.index',
//                'MenuPermissionName' => 'policyStatusFilterMaster.view',
                'front_end_url' => '',
                'isFrontEnd' => 'N'
            ],
            [
                'menu' => 'Qualification Master',
                'menuId' => $MasterId->id,
                'route' => 'qualification',
//                'MenuPermissionName' => 'policyStatusFilterMaster.view',
                'front_end_url' => '',
                'isFrontEnd' => 'N'
            ],


        ]);
        $UACID = MenuMasterModel::where('menu', 'User Access Control')->first();
        $insertUAC = MenuMasterModel::insert([
            [
                'menu' => 'User Type Master',
                'menuId' => $UACID->id,
                'route' => 'UserTypes.index',
//                'MenuPermissionName' => 'usertype.view',
                'front_end_url' => 'UserTypes',
                'isFrontEnd' => 'Y'
            ] ,
            [
                'menu' => 'Roles Master',
                'menuId' => $UACID->id,
                'route' => 'roles.index',
//                'MenuPermissionName' => 'role.view',
                'front_end_url' => 'Roles',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'AccessControl',
                'menuId' => $UACID->id,
                'route' => 'AccessControlView',
//                'MenuPermissionName' => 'UserAccessControl.view',
                'front_end_url' => 'AccessControl',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Menu Master',
                'menuId' => $UACID->id,
                'route' => 'MenuMaster',
//                'MenuPermissionName' => 'menu.view',
                'front_end_url' => 'MenuMaster',
                'isFrontEnd' => 'Y'
            ],
            [
                'menu' => 'Config Permission Mapping',
                'menuId' => $UACID->id,
                'route' => 'PermissionView',
//                'MenuPermissionName' => 'ConfigPermission.view',
                'front_end_url' => 'ConfigPermission',
                'isFrontEnd' => 'N'
            ]
        ]);
    }
}
