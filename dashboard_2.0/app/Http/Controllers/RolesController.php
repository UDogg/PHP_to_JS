<?php

namespace App\Http\Controllers;

use App\Http\Requests\RolesReq\Roles;
use App\Models\User;
use App\Models\userTypes;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Spatie\Permission\Models\Permission;
use Spatie\Permission\Models\Role;

class RolesController extends Controller
{
    protected $user_id;
    /**
     * Display a listing of the resource.
     */
    public  function __construct(Request $request)
    {
        $this->user_id = Auth::user();

    }


    public function index(Request $request)
    {
        $per_page = $request->per_page;
        $page = $request->page;
        $per_page = 10;
        $ReportingRolesData = Role::select('id', 'name', 'user_type', 'reporting_role');
        $ReportingRoles = $ReportingRolesData->paginate($per_page);
        $totalRecords = $ReportingRoles->total();
        $ReportingRolesArr  = array_column($ReportingRolesData->get()->toArray(), 'name', 'id');
        $userTypeData = userTypes::select('id', 'name')->where('is_active', 'Y')->get();
        $userType = $userTypeData->all();
        $userTypeArr  = array_column($userTypeData->toArray(), 'name', 'id');
        return view('UserAccessControl.Roles', compact('ReportingRoles', 'userType', 'userTypeArr', 'ReportingRolesArr', 'totalRecords', 'page', 'per_page'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        //

    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Roles $request)
    {
        $permission = credential_decrypt(config('Permission.role.edit'));
        if (!$this->user_id->can($permission)) {
            return  requestResponseMessage(['status' => '404', 'message' => 'Access Denied']);
        }

        $validated = $request->validate([
            'ReportingRole' => ['required', 'integer'],
            'RoleName'      => ['required', 'regex:/^[A-Za-z 0-9]+$/', 'max:30'],
            'UsertypeID'    => ['required', 'integer'],
        ]);
        
        
        $roleName   = $validated['RoleName'];
        $userType   = $validated['UsertypeID'];
        $reporting  = $validated['ReportingRole'];
        
        $role = Role::create([
            'name' => $roleName,
            'user_type' => $userType,
            'reporting_role' => $reporting

        ]);
        if ($role) {
            return response()->json([
                'status' => "true",
                'message' => 'Role Created Successfully',
            ]);
        }
        else
        {
             return  requestResponseMessage(['status' => '404', 'message' => 'Access Denied']);
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(Request $request)
    {
//        $permission = credential_decrypt(config('Permission.role.view'));
//        if (!$this->user_id->can($permission)) {
//            return  requestResponseMessage(['status' => '404', 'message' => 'Access Denied']);
//        }
        $userdetials = Auth::user();

        $currentRoledata = $userdetials->roles()->pluck('role_id','name')->toArray();
        $currentRole = reset($currentRoledata);
        $currentRoleName = key($currentRoledata);

        $isAdmin = $userdetials->is_admin;
        $usertypeId = $newUserRoleId = null;
        if($isAdmin == 'N')
        {
            $usertypeId = empty($request->usertype) ? $userdetials->usertype : $request->usertype;
            $newUserRoleId = empty($request->newroleId) ? $currentRole : $request->newroleId;
        }
        else
        {
            $usertypeId = $request->usertype;
            $newUserRoleId = $request->newroleId;
        }

        $mode = $request->mode;
        if($mode == 'roleEdit')
        {
            $currentRole = $request->role_id;
            $upperHierarchyRoles  = getRoleUpperHierarchy($currentRole);
            foreach ($upperHierarchyRoles as $key => $value) {
                unset($upperHierarchyRoles[$key]['user_type']);
                unset($upperHierarchyRoles[$key]['reporting_role']);
            }
            return response()->json([
                'status' => "true",
                'data' => $upperHierarchyRoles
            ]);
        }
        $nonAdminRoles = [];
        $loweRoles = [];
        

       $identifier = userTypes::where('id',$userdetials->usertype)->pluck('Identifier')->first();
       $creatingUsertype = userTypes::where('id',$request->usertype)->pluck('Identifier')->first();

         //IF E CREATE E P/P POS/POS
        if ($identifier == $creatingUsertype) {
            if (!empty($newUserRoleId) && !empty($usertypeId)) {
                $loweRoles = getRoleLowerHierarchy($newUserRoleId, $request->usertype);

                return response()->json([
                    'status' => "true",
                    'data' => $loweRoles
                ]);
            }
        }

        $rolesList = Role::select('id', 'name','reporting_role')->where('name', '!=', 'Super Admin')->where('id','!=',$currentRole);
        if ($request->has('usertype') && !empty($request->usertype)) {
            $rolesList = $rolesList->whereIn('user_type', [$request->usertype])->get();
        } else {
            $rolesList = $rolesList->get();
        }
        foreach ($rolesList as $key => $rolee)
        {
            $rolee->reporting_role = $rolee->reporting_role == 0 ? true : false;
            if(in_array($rolee->id,$loweRoles))
            {
                unset($rolesList[$key]);
                if($isAdmin == 'N')
                {
                    $nonAdminRoles[] = [
                        'id' => $rolee->id,
                        'name' => $rolee->name
                    ];

                }
            }
        }

        foreach($rolesList as $key ){
            $outputData[] = [
                'id' => $key->id,
                'name' => $key->name,
                'reporting_role' =>$key->reporting_role

            ];
        }

        return response()->json([
            'status' => "true",
            'data' => $outputData
        ]);
    }

    public function reportingUserReportsTo(Request $request)
    {
        $reportingTo = User::where('id', $request->user_id)->pluck('reportingto')->first() ?? null;
        $reportingToData = User::where('id', $reportingTo)->select('id', 'name')->first() ?? null;
        if(!empty($reportingToData)){
            $data = [];
            $data = [
                'id' => $reportingToData->id,
                'name' => credential_decrypt($reportingToData->name),
            ];
            return response()->json([
                'status' => "true",
                'data' => $data
            ]);
        }else {
            return response()->json([
                'status' => "false",
                'message' => "No Data Found",
                'data' => []
            ]);
        }
     
    }

    public function roleLowerHierarchyList(Request $request){
        
        $auth = Auth::user();

        if ($auth->usertype == 1 && $auth->is_admin == "Y") {
            $roleLowerHierarcyData = Role::select('id','name','user_type','reporting_role')->where('user_type',$request->usertype)->get();
        } else {
            $roleName = $auth->getRoleNames()->toArray();
            $roleId = Role::where('name', $roleName[0])->pluck('id')->first();
            $output = [];
    
            $roleLowerHierarcyData = getRoleLowerHierarchy($roleId, $request->usertype);


            $userTypeIdentifier  = userTypes::where('id',$request->usertype)->pluck('Identifier')->first();
            $authUserIdentifier = userTypes::where('id',$auth->usertype)->pluck('Identifier')->first();

            if(($authUserIdentifier == 'E' && $userTypeIdentifier == 'P' )|| ($authUserIdentifier == 'E' && $userTypeIdentifier == 'Partner')){
                $RoleData = Role::select('id','name','user_type','reporting_role')->where('user_type',$request->usertype)->get();
                $roleLowerHierarcyData = $RoleData;
            }
        }
        $roleLowerHierarcyData = collect($roleLowerHierarcyData);

        foreach ($roleLowerHierarcyData as $rlh) {
            $userTypeOfRole = Role::where('id', $rlh->reporting_role)->pluck('user_type')->first();

            // if ($rlh->reporting_role != 0 && $rlh->user_type == $userTypeOfRole) {
                $output[] = [
                    "id" => $rlh->id,
                    "name" => $rlh->name,
                    "user_type" => $rlh->user_type,
                    "reporting_role" => $rlh->reporting_role,
                ];
            // }
        }

        if (!empty($output)) {

            return response()->json([
                'status' => "true",
                'data' => $output
            ]);
        } else {
            return response()->json([
                'status' => "false",
                'message' => "No Data Found",
                'data' => []
            ]);
        }   
    }

    public function roleList(Request $request){
  
        $RoleData = Role::select('id','name','user_type','reporting_role')->where('user_type',$request->usertype)->get();

        // if ($request->usertype == 1) {
        //     $RoleData = $RoleData->reject(function ($role) {
        //         return $role->name == "Employee Admin";
        //     })->values(); 
        // }
        
        if (!empty($RoleData)) {
        
            return response()->json([
                'status' => "true",
                'data' => $RoleData
            ]);
        } else {
            return response()->json([
                'status' => "false",
                'message' => "No Data Found",
                'data' => []
            ]);
        }
    }

    public function rolesForReportConfigurator(Request $request){

       $user = Auth::user();

       $userType = [];

       if($user->usertype == 1){
        array_push($userType, 1, 2, 3);
       }elseif($user->usertype == 2){
        array_push($userType, 2);
       }elseif($user->usertype == 3){
        array_push($userType, 3);
       }


        $RoleData = Role::select('id','name','user_type','reporting_role')->whereIn('user_type',$userType)->get();

        if (!empty($RoleData)) {
        
            return response()->json([
                'status' => "true",
                'data' => $RoleData
            ]);
        } else {
            return response()->json([
                'status' => "false",
                'message' => "No Data Found",
                'data' => []
            ]);
        }
    }



    /**
     * Show the form for editing the specified resource.
     */
    public function edit(Request $request)
    {
        $validate = $request->validate([
            'id' => 'required|integer'  ,
            'RoleName' => 'required|string|max:75',
            'UsertypeID' => 'required|integer',
//            'ReportingRole' => 'required|integer',
        ]);

        if($request->id == $request->ReportingRole){
            return response()->json([
                'status' => "false",
                'message' => 'Role and Reporting Role Cannot be same',
            ]);
        }

        $role = Role::where('id', $request->id)->update([
            'name' => $request->RoleName,
            'user_type' => $request->UsertypeID,
            'reporting_role' => $request->ReportingRole
        ]);
        if ($role) {
            return response()->json([
                'status' => "true",
                'message' => 'Role Updated Successfully',
            ]);
        }
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        //
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(Request $request)
    {
        $permission = credential_decrypt(config('Permission.role.edit'));
        if (!$this->user_id->can($permission)) {
            return  requestResponseMessage(['status' => '404', 'message' => 'Access Denied']);
        }
        $request->validate([
            'id' => ['required', 'int']
        ]);
        $id  = $request->id;
        $deleteData  = Role::where('id', $id)->delete();
        if ($deleteData) {
            return response()->json([
                'status' => "true",
                'message' => 'Role Deleted Successfully',
            ]);
        }
    }
    public function UserRoleMapping(Request $request)
    {

        $roleId = $request->role_id;
        $userId = $request->user_id;
        $role = Role::findOrFail($roleId);

        $userId = User::findOrFail($userId);

        $AssignedRole = $userId->syncRoles($role);
        if ($AssignedRole) {
            return response()->json([
                'status' => "true",
                'message' => "Role Assigned SuccessFully"
            ]);
        } else {
            return response()->json([
                'status' => "false",
                'message' => "Error Occured in Role Assignment"
            ]);
        }
    }
    public function roleDetailsList(Request $request)
    {
        // $permissions = credential_decrypt(config('Permission.role.view'));
        // dd($permissions);
        // if (!$this->user_id->can($permissions))
        // {
        //     return  requestResponseMessage(['status' => '404', 'message' => 'Access Denied']);
        // }
        $role = Role::join('usertypes', 'usertypes.id', 'roles.user_type')
            ->join('roles as reporting_roles', 'reporting_roles.id', '=', 'roles.reporting_role')
            ->select('roles.id', 'roles.name', 'roles.user_type as user_type_id', 'roles.is_admin', 'usertypes.name as user_type', 'roles.reporting_role as reporting_role_id', 'reporting_roles.name as reporting_role_name')->where('usertypes.is_active', 'Y')->orderBy('roles.created_at', 'desc');

        if ($request->has('search') && !empty($request->search)) {
            $role->where(function ($query) use ($request) {
                $query->where('roles.name', 'LIKE', '%' . $request->search . '%')
                    ->orWhere('usertypes.name', 'LIKE', '%' . $request->search . '%')
                    ->orWhere('reporting_roles.name', 'LIKE', '%' . $request->search . '%');
            });
        }

        $role_id = $request->role_id;
        $mode = $request->mode;
        if ($role_id) {

            $role_instance = $role->where('roles.id', $role_id)->first();
            $role_data = $role_instance->toArray();
            if(!empty($mode) && $mode == 'roleEdit')
            {
                return response()->json([
                    'status' => 200,
                    "return_data" => $role_data,
                    'message' => "Role Details Data Found"
                ]);
            }


            if ($role_instance) {
                $permissions = $role_instance->permissions;

                $role_data = $role->where('roles.id', $role_id)->first();

                if ($role_data) {
                    $role_data = $role_data->toArray();
                    $role_data['permissions'] = $permissions;

                    return response()->json([
                        'status' => 200,
                        "return_data" => $role_data,
                        'message' => "Role Details Data Found"
                    ]);
                }
            }

            return response()->json([
                'status' => 500,
                'return_data' => [],
                "message" => "No Data Found"
            ], 500);
        } else {
            // If no role_id is provided, fetch all roles
            $per_page = $request->perPage ?? 10;
            $page = $request->page ?? 1;
            $configEnabled = config('B2C.ROLE.CODE.MAPPING') == 'true';
            if(($request->has('search') && !empty($request->search)) && $page>1){
                $role_data = [];
                $roles = $role->get();
                $index = 1;
                foreach ($roles as $role_instance) {
                     $role_instance_data = $role_instance->toArray();
                     $role_instance_data['role_code_mapping'] = ($configEnabled && $role_instance_data['user_type'] == "B2C");   

                    $role_instance_data['Sr_no'] = $index;
                    $index++;

                    // Fetch permissions for each role
                    $permissions = Role::findById($role_instance->id, 'sanctum')->permissions;
                    $role_instance_data['permissions'] = $permissions;

                    $role_data[] = $role_instance_data;
                }
                return response()->json([
                    'status' => 200,
                    "return_data" => $role_data,
                    'message' => "Role Details Data Found"
                ]);
            }
            $roles = $role->paginate($per_page);

            $lastPage = $roles->lastPage();
            $totalData = $roles->total();
            $startingIndex = ($roles->currentPage() - 1) * $roles->perPage() + 1;
            if ($roles->isNotEmpty()) {
                $role_data = [];
                $index = $startingIndex;

                foreach ($roles as $role_instance) {
                     $role_instance_data = $role_instance->toArray();
                     $role_instance_data['role_code_mapping'] = ($configEnabled && $role_instance_data['user_type'] == "B2C");   

                    $role_instance_data['Sr_no'] = $index;
                    $index++;

                    // Fetch permissions for each role
                    $permissions = Role::findById($role_instance->id, 'sanctum')->permissions;
                    $role_instance_data['permissions'] = $permissions;

                    $role_data[] = $role_instance_data;
                }

                return response()->json([
                    'status' => 200,
                    "return_data" => $role_data,
                    'message' => "Role Details Data Found",
                    'pagination' => [
                    'per_page' => $per_page,
                    'page' => $page,
                    'total' => $totalData,
                    'last_page' => $lastPage,
            ]
                ]);
            }

            return response()->json([
                'status' => 500,
                'return_data' => [],
                "message" => "No Data Found"
            ], 500);
        }
    }
    public function CreateClone(Request $request)
    {
        $validate = $request->validate([
//           'usertype' => 'required',
           'roleId' => 'required',
           'newRoleId' => 'required',
        ]);
        $rolePermissions = Role::findById( $request->roleId);
        $permissionsList = $rolePermissions->permissions;

        foreach($request->newRoleId as $nRoleId)
        {
            $newRoleName = Role::findById($nRoleId);
            foreach($permissionsList as $list)
            {
                $newRoleName->givePermissionTo($list->name);
            }

        }
        return response()->json([
            'status' => "true",
            'message' => 'Role Cloned Successfully',
        ]);
    }

    public function getReportingRoleData(Request $request){
        $user = Auth::user();
        $newRoleId = $request->role_id;
        $filteredRoles=[];
        
        // dd($request->user_type);

        if($request->user_type != 1){
            // $roles = DB::table('roles')
            // ->select('name','id','user_type','reporting_role')
            // ->where('user_type', 1)
            // ->orWhere('user_type', $request->user_type)
            // ->get();

            // // dd($roles);

            // foreach($roles as $key => $role){
            //     if($role->user_type == 1){
            //         $filteredRoles[$key] = $role;
            //     }
            // }

            $hierarchyArray = getRoleUpperHierarchy($newRoleId);
            // dd($hierarchyArray);
            // $arrayFilteredRoles = (array)$filteredRoles;
            // $mergedArray = [...$arrayFilteredRoles, ...$hierarchyArray];

            return $hierarchyArray;


        }else{
            $hierarchyArray = getRoleUpperHierarchy($newRoleId);
            return $hierarchyArray;
        }
    }

    public function reportingRoleNew(Request $request){;

        $user = Auth::user();
        $Role = $user->getRoleNames()->toArray();
        $roleIdOfLoggedInUser = Role::where('name', $Role[0])->pluck('id')->first();
        $newRoleId = $request->role_id;
        $hierarchyArray = collect(array_merge(
            getRoleUpperHierarchyTillLoggedInUser($newRoleId, $roleIdOfLoggedInUser),
            Role::where('user_type', $request->user_type)->where('id', '!=', $request->role_id) ->get(['id','name','user_type','reporting_role'])->toArray()))->unique('id')->values()->all();


        $userTypeIdentifier  = userTypes::where('id',$request->user_type)->pluck('Identifier')->first();

        if ($userTypeIdentifier == 'P' || $userTypeIdentifier == 'Partner') {
            $rolesToExclude = ['Employee Admin'];
            $hierarchyArray = array_values(array_filter($hierarchyArray, function ($role) use ($rolesToExclude) {
                return !in_array($role['name'], $rolesToExclude);
            }));
        }

        if($user->is_admin == 'Y' && $user->usertype == 1 && ($userTypeIdentifier == 'P' || $userTypeIdentifier == 'Partner') ){
            $posRole=Role::select('id', 'name', 'user_type', 'reporting_role')->where('user_type',1)->get()->toArray();
            $hierarchyArray = array_merge($hierarchyArray,$posRole);
        }elseif($user->is_admin == 'N' && $user->usertype == 1 && ($userTypeIdentifier == 'P' || $userTypeIdentifier == 'Partner') ){
            $posRole=Role::select('id', 'name', 'user_type', 'reporting_role')->where('id', $roleIdOfLoggedInUser)->get()->toArray();
            $hierarchyArray = array_merge($hierarchyArray,$posRole);
        }
        
        return $hierarchyArray;
    }

    public function reportingEmployeeForPosAndPartner(Request $request)
    {
        $reportingEmployeeData = [];
        $auth = Auth::user();
        $user_type_of_authenticated_user = userTypes::where('id',$auth->usertype)->pluck('Identifier')->first();

        if ($user_type_of_authenticated_user == 'E') {
            $reportingEmployeeData = [
                'id' => $auth->id,
                'name' => credential_decrypt($auth->name),
            ];
            if(!empty($reportingEmployeeData)){
                return response()->json([
                    'status' => "true",
                    'data' => $reportingEmployeeData
                ]);
            }else{
                return response()->json([
                    'status' => "false",
                    'message' => "No Data Found",
                    'data' => []
                ]);

            }
        } else {
            $employee_code = User::where('id', $request->id)->pluck('employee_code')->first() ?? null;
            $reportingEmployeeData = User::select('id', 'name')->where('employee_code', $employee_code)->where('usertype', '1')->first() ?? null;
        }

        if (!empty($reportingEmployeeData)) {
            $reportingEmployee = [];
            $reportingEmployee = [
                'id' => $reportingEmployeeData->id,
                'name' => credential_decrypt($reportingEmployeeData->name),
            ];
            return response()->json([
                'status' => "true",
                'data' => $reportingEmployee
            ]);
        } else {
            return response()->json([
                'status' => "false",
                'message' => "No Data Found",
                'data' => []
            ]);
        }

    }

    public function searchRoles(Request $request)
    {
        $role = Role::join('usertypes', 'usertypes.id', 'roles.user_type')
            ->join('roles as reporting_roles', 'reporting_roles.id', '=', 'roles.reporting_role')
            ->select(
                'roles.id',
                'roles.name',
                'roles.user_type as user_type_id',
                'usertypes.name as user_type',
                'roles.reporting_role as reporting_role_id',
                'reporting_roles.name as reporting_role_name'
            )
            ->where('usertypes.is_active', 'Y');

        $headerKey = $request->header_key;
        $searchValue = $request->search_value;

        $allowedColumns = [
            'roles.id',
            'roles.name',
            'roles.user_type',
            'usertypes.name',
            'roles.reporting_role',
            'reporting_roles.name'
        ];

        if ($headerKey && $searchValue) {
            $matchingColumn = collect($allowedColumns)->first(fn($column) => str_contains($column, $headerKey));

            if ($matchingColumn) {
                $role->where($matchingColumn, 'LIKE', "%{$searchValue}%");
            } else {
                return response()->json(['status' => 400, 'message' => 'Invalid header_key provided.'], 400);
            }
        }

        $roles = $role->get();

        return $roles->isNotEmpty()
            ? response()->json(['status' => 200, "return_data" => $roles, 'message' => "Search Results Found"])
            : response()->json(['status' => 500, 'return_data' => [], "message" => "No Data Found"], 500);
    }

}
