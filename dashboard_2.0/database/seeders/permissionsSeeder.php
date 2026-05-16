<?php

namespace Database\Seeders;

use App\Models\Credential;
use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;
use Illuminate\Support\Facades\DB;

class permissionsSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $childMenus = DB::table('MenuMaster')->where('menuId','!=',null)->select('menu')->get();
        $types = ['view','edit','upload','delete'];
        foreach ($childMenus as $childMenu) {
            foreach ($types as $type) {
                \Spatie\Permission\Models\Permission::create(['name' => $childMenu->menu.'.'.$type, 'guard_name' => 'sanctum']);
            }
        }
        $parentMenusPermissions = DB::table('MenuMaster')->where('menuId',null)->where('is_child','N')->select('menu')->get();
        foreach ($parentMenusPermissions as $parentMenu) {
            foreach ($types as $type) {
                \Spatie\Permission\Models\Permission::create(['name' => $parentMenu->menu.'.'.$type, 'guard_name' => 'sanctum']);
            }
        }
        $permissionConfig = [
            [
                'name' => 'Permission.user.view',
                'value' => 'Users.view'
            ],
            [
                'name' => 'Permission.user.edit',
                'value' => 'Users.edit'
            ],
            [
                'name' => 'Permission.user.upload',
                'value' => 'Users.upload'
            ],
            [
                'name' => 'Permission.user.delete',
                'value' => 'Users.delete'
            ],
            [
                'name' => 'Permission.role.view',
                'value' => 'Roles Master.view'
            ],
            [
                'name' => 'Permission.role.edit',
                'value' => 'Roles Master.edit'
            ],
            [
                'name' => 'Permission.role.upload',
                'value' => 'Roles Master.upload'
            ],
            [
                'name' => 'Permission.role.delete',
                'value' => 'Roles Master.delete'
            ],
            [
                'name' => 'Permission.Access.view',
                'value' => 'AccessControl.view'
            ],
            [
                'name' => 'Permission.Access.edit',
                'value' => 'AccessControl.edit'
            ],
            [
                'name' => 'Permission.Access.upload',
                'value' => 'AccessControl.upload'
            ],
            [
                'name' => 'Permission.Access.delete',
                'value' => 'AccessControl.delete'
            ],

            [
                'name' => 'Permission.Dashboard.view',
                'value' => 'Dashboard.view'
            ],
            [
                'name' => 'Permission.Dashboard.edit',
                'value' => 'Dashboard.edit'
            ],
            [
                'name' => 'Permission.Dashboard.upload',
                'value' => 'Dashboard.upload'
            ],
            [
                'name' => 'Permission.Dashboard.delete',
                'value' => 'Dashboard.delete'
            ],
            [
                'name' => 'Permission.Sellnow.view',
                'value' => 'Sell Now.view'
            ],
            [
                'name' => 'Permission.Sellnow.edit',
                'value' => 'Sell Now.edit'
            ],
            [
                'name' => 'Permission.Sellnow.upload',
                'value' => 'Sell Now.upload'
            ],
            [
                'name' => 'Permission.Sellnow.delete',
                'value' => 'Sell Now.delete'
            ],
            [
                'name' => 'Permission.PolicyStatusReport.view',
                'value' => 'Policy Status Report.view'
            ],
            [
                'name' => 'Permission.PolicyStatusReport.edit',
                'value' => 'Policy Status Report.edit'
            ],
            [
                'name' => 'Permission.PolicyStatusReport.upload',
                'value' => 'Policy Status Report.upload'
            ],
            [
                'name' => 'Permission.PolicyStatusReport.delete',
                'value' => 'Policy Status Report.delete'
            ],
            [
                'name' => 'Permission.PolicyReportFilterMaster.view',
                'value' => 'Policy Report Filter Master.view'
            ],
            [
                'name' => 'Permission.PolicyReportFilterMaster.edit',
                'value' => 'Policy Report Filter Master.edit'
            ],
            [
                'name' => 'Permission.PolicyReportFilterMaster.upload',
                'value' => 'Policy Report Filter Master.upload'
            ],
            [
                'name' => 'Permission.PolicyReportFilterMaster.delete',
                'value' => 'Policy Report Filter Master.delete'
            ],
            [
                'name' => 'Permission.delegate.view',
                'value' => 'Delegate.view'
            ],
            [
                'name' => 'Permission.delegate.edit',
                'value' => 'Delegate.edit'
            ],
            [
                'name' => 'Permission.delegate.delete',
                'value' => 'Delegate.delete'
            ],
            [
                'name' => 'Permission.LoginHistory.view',
                'value' => 'Login History.view'
            ],
            [
                'name' => 'Permission.LoginHistory.edit',
                'value' => 'Login History.edit'
            ],
            [
                'name' => 'Permission.LoginHistory.upload',
                'value' => 'Login History.upload'
            ],
            [
                'name' => 'Permission.LoginHistory.delete',
                'value' => 'Login History.delete'
            ],
            [
                'name' => 'Permission.TemplateList.view',
                'value' => 'Template List.view'
            ],
            [
                'name' => 'Permission.TemplateList.edit',
                'value' => 'Template List.edit'
            ],
            [
                'name' => 'Permission.TemplateList.upload',
                'value' => 'Template List.upload'
            ],
            [
                'name' => 'Permission.TemplateList.delete',
                'value' => 'Template List.delete'
            ],
            [
                'name' => 'Permission.OfflinePolicy.view',
                'value' => 'Offline Policy.view'
            ],
            [
                'name' => 'Permission.OfflinePolicy.edit',
                'value' => 'Offline Policy.edit'
            ],
            [
                'name' => 'Permission.OfflinePolicy.upload',
                'value' => 'Offline Policy.upload'
            ],
            [
                'name' => 'Permission.OfflinePolicy.delete',
                'value' => 'Offline Policy.delete'
            ],
            [
                'name' => 'Permission.configuration.view',
                'value' => 'Configuration.view'
            ],
            [
                'name' => 'Permission.configuration.edit',
                'value' => 'Configuration.edit'
            ],
            [
                'name' => 'Permission.configuration.upload',
                'value' => 'Configuration.upload'
            ],
            [
                'name' => 'Permission.configuration.delete',
                'value' => 'Configuration.delete'
            ],


        ];
        $configPermissionGroup = DB::table('ConfigMaster')->insertGetId([
            'key' => 'Permissions',
        ]);

        foreach ($permissionConfig as $permission) {

            $crendetialPermissions = Credential::insert([
               'credential_label' => 'Permissions',
                'credential_key' => $permission['name'],
                'credential_value' => credential_encrypt($permission['value']),
                'configuration' => $configPermissionGroup,
                'enviroment' => 'local',
                'created_at' => now(),
            ]);
        }
    }
}
