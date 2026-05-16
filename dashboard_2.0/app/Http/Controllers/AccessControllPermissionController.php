<?php

namespace App\Http\Controllers;

use App\Http\Requests\PermissionReq;
use App\Models\AccessControlPermissions;
use App\Models\MenuMasterModel;
use App\Models\User;
use App\Models\Customer;
use App\Models\userTypes;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Spatie\Permission\Models\Permission;
use Spatie\Permission\Models\Role;
use App\Models\TokenModel;

class AccessControllPermissionController extends Controller
{
    //
    public $user;
    public function __construct()
    {
        $this->user = Auth::user();

    }
    public  function index()
    {
        $permission = credential_decrypt(config('Permission.Access.view'));
        if(!$this->user->can($permission))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }

        $per_page = 1000;

        $rolesData = Role::select('id','name','user_type');

        $permissionRolesMappingData = DB::table('role_has_permissions')->join('permissions','permissions.id','=','role_has_permissions.permission_id')->join('roles','roles.id','=','role_has_permissions.role_id')->select( 'permissions.id as permission_id',
            'permissions.name as permission_name',
            'roles.id as role_id',
            'roles.name as role_name')->paginate($per_page)->toArray();
        $collect = collect($permissionRolesMappingData['data']);
        $dataPermission  = $collect->groupBy('permission_name')->all();
        $data_role  = $collect->groupBy('role_name')->all();

        $roles = $rolesData->get()->all();
        $permissions = Permission::select('id','name')->get()->all() ?? [];
        return view('UserAccessControl.AccessPermission',compact('roles','permissions','permissionRolesMappingData','dataPermission'));
    }


    public function giveAccess(PermissionReq $request)
    {
        $permission = credential_decrypt(config('Permission.Access.edit'));
        if(!$this->user->can($permission))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $currentRole = $this->user->roles()->pluck('role_id')[0];

        if($currentRole == $request->role_id)
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $permission = $request->permission_id;
        $role_id = $request->role_id;
        $permission = Permission::whereIn('id',$permission)->get();
        $role = Role::where('id',$role_id)->first();
        foreach ($permission as $key => $value)
        {
            $AssignedRole = $role->givePermissionTo($value->id);
        }
        if($AssignedRole)
        {
            return response()->json([
                'status' => "true",
                'message' => "Permission Assigned SuccessFully"
            ]);


        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => "Error Occured in Permission Assignment"
            ]);
        }

    }
    public  function destroy(Request $request)
    {
        $permission = credential_decrypt(config('Permission.Access.edit'));
        if(!$this->user->can($permission))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $permission = Permission::where('id',$request->permission_id)->delete();
        if($permission)
        {
            return response()->json([
                'status' => "true",
                'message' => "Permission Deleted SuccessFully"
            ]);
        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => "Error Occured in Permission Deletion"
            ]);
        }
    }
    public  function revokePermission(Request $request)
    {
        $currentRole = $this->user->roles()->pluck('role_id')[0];
        if($currentRole == $request->role_id)
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $permission = credential_decrypt(config('Permission.Access.edit'));
        if(!$this->user->can($permission))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $permission = Permission::where('id',$request->permission_id)->first();
        $role = Role::where('id',$request->role_id)->first();
        $revokePermission = $role->revokePermissionTo($permission);
        if($revokePermission)
        {
            return response()->json([
                'status' => "true",
                'message' => "Permission Revoked SuccessFully"
            ]);
        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => "Error Occured in Permission Revocation"
            ]);
        }

    }
    public static function getPermissions(Request $request)
    {
        if(!empty($request->role_id))
        {
            $role_id = $request->role_id;
            $roles = Role::with('permissions')->findOrFail($role_id);
            $permissions = $roles->permissions->toArray();
            foreach ($permissions as $key => $value)
            {
                $data[] = [
                    'id' => $value['id'],
                    'name' => $value['name']
                ];
            }
            if(!empty($permissions))
            {
                return response()->json([
                    'status' => "true",
                    'data' => $data
                ]);
            }
            else
            {
                return response()->json([
                    'status' => "false",
                    'message' => "Permission Not Found"
                ]);
            }

        }
        else
        {
            $permissions  = Permission::select('id','name')->get()->all();
        }
        if(!empty($permissions))
        {
            return response()->json([
                'status' => "true",
                'data' => $permissions
            ]);
        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => "Permission Not Found"
            ]);
        }
    }

    public function UserPermissions(Request $request)
    {
        $permission = credential_decrypt(config('Permission.Access.view'));
        if(!$this->user->can($permission))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        if($request->has('userId'))
        {
           $validate =  $request->validate([
                'userId' => 'integer'
            ],[
                'userId.integer' => 'Please Enter Valid User Id!!!'
           ]);

            $user = User::find($request->userId);
            if(empty($user))
            {
                return response()->json([
                    'status' => 404,
                    'message' => 'User Not Found'
                ]);
            }
            else
            {
                $permissionNames  = $user->getAllPermissions()->toArray();
            }
        }
        if($request->has('roleId'))
        {
            $validate =  $request->validate([
                'roleId' => 'integer'
            ],[
                'roleId.integer' => 'Please Enter Valid Role Id!!!'
            ]);
            $role = Role::find($request->roleId);
            if(empty($role))
            {
                return response()->json([
                    'status' => 404,
                    'message' => 'Role Not Found'
                ]);
            }
            else
            {
                $permissionNames  = $role->permissions;
            }
        }
        else
        {
            $user = User::find($this->user->id);
            $rolenames =  $user->getRoleNames();
            $role = Role::findByName($rolenames[0]);
            $permissionNames  = $role->permissions;

        }
        $allMenus = MenuMasterModel::select('id','menu','menuId','subMenuId','isFrontEnd','is_child')->get()->toArray();
        $allMenucollect = collect($allMenus);
        $parentMenus = $allMenucollect->filter(function ($menu) {
            return $menu['menuId'] == '' || $menu['is_child'] == 'N';
        })->toArray();
        foreach ($parentMenus as $value)
        {
            $childMenus = $allMenucollect->filter(function ($menu) use ($value) {
                return  $menu['menuId'] == $value['id'] && $menu['isFrontEnd'] == 'Y';
            });
            $value['subMenus'] = $childMenus->toArray();
            $newMenuArr[] = $value;
        }
        $finalMenus = [];
        $allPermissions = Permission::select('id','name')->get()->toArray();
        $allPermissions = array_column($allPermissions,'name','id');

        foreach ($permissionNames as $menusData)
        {
            if(in_array($menusData['name'], $allPermissions))
            {
                unset($allPermissions[$menusData['id']]);
            }
            list($menus,$permissionNames) = explode('.',$menusData['name']);
            $temp_arr[$menus] = [$menusData['id'],$permissionNames];
            foreach ($temp_arr as $key => $item)
            {
                if (!isset($finalMenus[$key]))
                {
                    $finalMenus[$key] = [];
                }
                $finalMenus[$key][] = [
                    "id" => $item[0],
                    'name' => $item[1],
                    'isChecked' => 1
                ];
            }
            $temp_arr = [];
        }
        $newallPermission =  [];
        foreach($allPermissions as $allperKey => $allPer)
        {
            list($allmenu, $allper) = array_pad(explode('.', $allPer, 2), 2, null);
            $newallPermission[$allmenu][]= ['id' => $allperKey,
                'name' => $allper,
                'isChecked' => 0
            ];
        }
        foreach ($newMenuArr as $key => $value)
        {
            $val['permissions'] = [];
            $indexedSubMenus = [];
            if(empty($value['subMenus']) && $value['is_child'] == 'Y')
            {
                unset($newMenuArr[$key]);
                continue    ;
            }
            if(empty($value['subMenus']) && $value['is_child'] == 'N')
                {
                    if(array_key_exists($value['menu'], $finalMenus))
                        {
                            $newMenuArr[$key]['permissions'] = $finalMenus[$value['menu']];
//                            continue;
                        }else {
                            $newMenuArr[$key]['permissions'] = [];
                        }
                    if(array_key_exists($value['menu'], $newallPermission))
                    {
                        $notassignedPermissions = $newallPermission[$value['menu']];
                        $newMenuArr[$key]['permissions'] = !empty($newMenuArr[$key]['permissions']) ? array_merge($newMenuArr[$key]['permissions'], $notassignedPermissions) : $notassignedPermissions;

//                        $val['permissions']=  array_merge($val['permissions'], $notassignedPermissions);
                    }
                }
            foreach($value['subMenus'] as $keyin => $val)
            {

                if(array_key_exists($val['menu'], $finalMenus))
                {
                    $menuPermissions = $finalMenus[$val['menu']];
                    $val['permissions']= $menuPermissions;
                }
                else
                {
                    $val['permissions'] = [];
                }
                if(array_key_exists($val['menu'], $newallPermission))
                {
                    $notassignedPermissions = $newallPermission[$val['menu']];

                    $val['permissions']=  array_merge($val['permissions'], $notassignedPermissions);
                }
                $indexedSubMenus[] = $val;

            }
            $newMenuArr[$key]['subMenus'] = $indexedSubMenus;
        }
        $newMenuArr = array_values($newMenuArr);

        if(!empty($finalMenus))
        {
            return response()->json([
                'status' => 200,
                'data' => $newMenuArr
            ]);
        }
        else
        {
            return response()->json([
                'status' => 200,
                'message' => 'User Does Not Have Any Permission',
                'data' => $newMenuArr
            ]);
        }
    }
    public function userMenus()
    {
        $authUser = Auth::user();
        $user = $authUser->usertype == "5"
        ? Customer::find($authUser->id)
        : User::find($authUser->id);
        // $user = User::find($this->user->id);

        $user->usertype = $authUser->usertype;
        $currentToken = $authUser->currentAccessToken();
        $journeyMenus = [];

        if (config("ippb_view_transaction")) {

            $plainToken = (request()->bearerToken()) ?? request()->bearerToken();
            $tokenData = TokenModel::where('token', $plainToken)->latest()->first();

            if ($tokenData && !empty($tokenData->decrypted_form_data)) {
                $formData = json_decode($tokenData->decrypted_form_data, true);
                if (!empty($formData['journey_type']) && $formData['journey_type'] == 'view_transaction') {
                    $journeyMenus = ['Profile','Dashboard','Policy Status'];
                }
                elseif (!empty($formData['journey_type']) && $formData['journey_type'] == 'sell_now') {
                    $journeyMenus = ['Sell Now'];
                }
            }
        }
        $switch     = getParsedAbilityValue($currentToken, 'switch:');
        $userRoleId   = getParsedAbilityValue($currentToken, 'userRole:');

        if ($userRoleId && $switch == 'true') {
            $role = Role::findById($userRoleId);
        }else{
            // $rolenames =  $user->getRoleNames()->toArray();
            $rolenames =  $authUser->userRoles()
                            ->where('user_type', $authUser->usertype)
                            ->get();
         
                if($rolenames->isNotEmpty())
                {
                    $role = Role::findByName($rolenames[0]->name);

                }
                else
                {
                    return response()->json([
                        'status' => 404,
                        
                        'message' => 'User Does Not Have Role Not Found'
                    ]);
                }
        }

        
        $userType = !empty($user->usertype) ? userTypes::find($authUser->usertype)->name : '';
 
        $newMenuArr = [];
        $permissionNames  = $role->permissions; 
        $allMenus = MenuMasterModel::select('id','menu','menuId','subMenuId','front_end_url','icon','isFrontEnd','is_child','order_by')->orderByRaw('ISNULL(order_by), order_by ASC')->get()->toArray();
        $allMenucollect = collect($allMenus);
        if (!empty($journeyMenus)) {

            $allowedMenus = collect($allMenus)
                ->whereIn('menu', $journeyMenus);

            $parentIds = $allowedMenus->pluck('menuId')->filter()->toArray();

            $allMenucollect = collect($allMenus)->filter(function ($menu) use ($journeyMenus, $parentIds) {
                return in_array($menu['menu'], $journeyMenus)
                    || in_array($menu['id'], $parentIds);
            })->values();
        }
        
        $allMenucollect = $allMenucollect->map(function ($menu) use ($userType) {
            $menu['front_end_url'] = !empty($userType) ? $userType.'/'.$menu['front_end_url'] : $menu['front_end_url'];
            $menu['is_child'] == 'Y' ? $menu['is_child'] = 1 : $menu['is_child'] = 0;

            return $menu;
        });
        if (is_array($currentToken->abilities) && isset($currentToken->abilities['delegate'])) {
            $delegateData = $currentToken->abilities['delegate'];
            $delegateInfo = [
                'delegate_user_id' => $delegateData['delegate_user_id'] ?? null,
                'delegate_username' => $delegateData['delegate_username'] ?? null,
            ];
        
            if (!$delegateInfo['delegate_user_id'] || !$delegateInfo['delegate_username']) {
                return requestResponseMessage([
                    'status' => 500,
                    'message' => 'Incomplete delegate data in token abilities'
                ]);
            }
        }else {
            $delegateInfo = [
                'delegate_user_id' => null,
                'delegate_username' => null,
            ];
        }
        $parentMenus = $allMenucollect->filter(function ($menu) use ($currentToken, $delegateInfo) {
            $isDelegate = $this->user->Is_delegate == 'Y';
            $delegateUserId = $delegateInfo['delegate_user_id'];
            if(!empty($this->user->reportingto) && $this->user->Is_delegate == 'N')
            {
                if($menu['menu'] == 'Delegate')
                {
                    return false;
                }
            }
            if ($delegateUserId !== null && $isDelegate) {
                if ($menu['menu'] == 'Sell Now') {
                    return false;
                }
            }
            return $menu['menuId'] == '' && $menu['subMenuId'] == '' && $menu['isFrontEnd'] == 'Y';
        })->toArray();
        foreach ($parentMenus as $value)
        {
            $childMenus = $allMenucollect->filter(function ($menu) use ($value) {
                return  $menu['menuId'] == $value['id'] && $menu['isFrontEnd'] == 'Y';
            });
            $lastMenus = $allMenucollect->filter(function ($menu) use ($value) {
                return  $menu['subMenuId'] == $value['id'];
            });
            if(!$user->usertype == 0)
            {
                $value['subMenus'] = $childMenus->toArray();
//                $value['subMenus']['last'] = $lastMenus->toArray();
            }
            else
            {
                $value['subMenus'] = array_values($childMenus->toArray());
//                $value['subMenus']['last'] = array_values($lastMenus->toArray());
            }
            $newMenuArr[] = $value;
        }
        $finalMenus = [];
        if(!$user->usertype == 0)
        {

            foreach ($permissionNames as $menusData) {
                list($menus,$permissionNames) = explode('.',$menusData['name']);
                $temp_arr[$menus] = $permissionNames;
                foreach ($temp_arr as $key => $item)
                {
                    if (!isset($finalMenus[$key])) {
                        $finalMenus[$key] = [];
                    }
                    $finalMenus[$key][] = $item;
                }
                $temp_arr = [];
            }
            foreach ($newMenuArr as $key => $value)
            {
                $indexedSubMenus = [];


                if(empty($value['subMenus']) && $value['is_child'] == 0)
                {
                    if(array_key_exists($value['menu'], $finalMenus))
                    {
                        $newMenuArr[$key]['permissions'] = $finalMenus[$value['menu']];
                        continue;
                    }else {
                        $newMenuArr[$key]['permissions'] = [];
                    }
                }
                    foreach($value['subMenus'] as $keyin => $val)
                    {
                        if(array_key_exists($val['menu'], $finalMenus))
                        {
                            $menuPermissions = $finalMenus[$val['menu']];
                            $val['permissions'] = $menuPermissions;
                            $indexedSubMenus[] = $val;
                        }
                        else
                        {
                            unset($newMenuArr[$key]['subMenus'][$keyin]);
                        }

                    }
                    $newMenuArr[$key]['subMenus'] = [];
                    if (!empty($indexedSubMenus))
                    {
                        $newMenuArr[$key]['subMenus'] = $indexedSubMenus;
                    }
                $newMenuArr = array_values($newMenuArr);


            }

            foreach ($newMenuArr as $key => $value) {

                if (!isset($value['menu'])) {
                    unset($newMenuArr[$key]);
                    continue;
                }
                if ($value['is_child']==0 && empty($value['permissions'])) {
                    unset($newMenuArr[$key]);
                }
                if ($value['is_child']==1 && empty($value['subMenus'])) {
                    unset($newMenuArr[$key]);
                }

            }

            foreach ($newMenuArr as $key => &$value) {

                if (isset($value['menu']) && $value['menu'] == "Sell Now" && $authUser->usertype == 5) {
                    $value['menu'] = "Buy Now";
                }

            }
            
            $newMenuArr = array_values($newMenuArr);
        }
        else
        {
            $finalMenus[] = 'super Admin';
        }

        if(!empty($finalMenus))
        {
            return response()->json([
                'status' => 200,
                'data' => $newMenuArr
            ]);
        }
        else
        {
            return response()->json([
                'status' => 200,
                'message' => 'User Does Not Have Any Permission',
                'data' => $newMenuArr
            ]);
        }
    }

    public function getDataByFilter(Request $request)
    {

        if (!empty($request->role_id)) {
            $results = DB::table('role_has_permissions as a')
            ->join('permissions as b', 'a.permission_id', '=', 'b.id')
            ->join('roles as c', 'a.role_id', '=', 'c.id')
            ->where('a.role_id', ($request->role_id ?? ""))
            ->where('c.id', $request->role_id ?? "")
            ->select('c.name as role_name', 'b.name as permission_name','b.id as permission_id')
            ->get();

            if (!empty($results)) {
                return ([
                    'status' => 200,
                    'data' => $results
                ]);
            } else {
                return ([
                    'status' => 404,
                    'message' => 'Data Not Found'
                ]);
            }
        } else {

            return ([
                'status' => 404,
                'message' => 'Data Not Found'
            ]);
        }
    }
    public function deleteData(Request $request)
    {
        if (!empty($request->permission_id)) {
            $permission_id = $request->permission_id;
            $data = Permission::where('id', $permission_id)->delete();

            if (!empty($data)) {
                return ([
                    'status' => 200,
                    'message' => 'Data Deleted Successfully'
                ]);
            } else {

                return ([
                    'status' => 404,
                    'message' => 'Data Not Found'
                ]);
            }
        } else {
            return ([
                'status' => 404,
                'message' => 'Data Not Found'
            ]);
        }
    }

}
