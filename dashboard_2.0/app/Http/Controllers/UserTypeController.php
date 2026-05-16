<?php

namespace App\Http\Controllers;

use App\Http\Requests\userTypeReq;
use App\Http\Requests\UsertypeUpdtReq;
use App\Models\User;
use App\Models\UserAccessManagment;
use App\Models\userTypes;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Log;
use Spatie\Permission\Models\Role;

class UserTypeController extends Controller
{

    public function __construct(Auth $auth)
    {
        $this->auth = $auth::user();
    }
    /**
     * Display a listing of the resource.
     */
    public function index(Request $request)
    {
//        $permission = config('Permission.usertype.view');
//        if (!$this->auth->can($permission)) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        $paginate = $request->paginate ?? 10;
        $search_val = $request->search_val;
        $Query =  userTypes::select('id','name','Identifier','created_at', 'is_active');
        $count = $Query->count();
        if($search_val)
        {
            $AllUsertype = $Query->where('name','like','%'.$search_val.'%')->paginate($paginate)->all();
        }
        else
        {
            $AllUsertype = $Query->paginate($paginate)->all();
        }
        $users = Usertypes::select('usertypes.*', 'users.username as username')
        ->join('users', 'usertypes.id', '=', 'users.usertype')
        ->where('users.is_admin', 'Y')
        ->get();
    

        foreach ($users as $user) {
            try {
                $user->username = credential_decrypt($user->username); // Decrypt username
            } catch (\Exception $e) {
                $user->username = '[Decryption Failed]'; // Handle errors
            }
            //  dd($user->username, ":" ,$user->password);
        }
        // dd($users);
        return view('UserAccessControl.UserType',compact('AllUsertype','count','users'));
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
    public function store(userTypeReq $request)
    {
//        $permission = config('Permission.usertype.edit');
//        if (!$this->auth->can($permission)) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        $create = userTypes::create([
            'name' => $request->UserType,
            'Identifier' => $request->Userident
        ]);
        $usertypeId = $create->id;
        if($create)
        {
            // creating the admin user for each usertype
            $user = User::insert([
                'name' => $request->UserType . ' Admin',
                'username' => $request->UserType . 'Admin',
                'email' => $request->UserType . 'Admin' . '@' . 'fyntune'. '.com',
                'password' => bcrypt('Admin@1234'),
                'mobile' => '1234567890',
                'address' => 'Admin Address',
                'pincode' => '123456',
                'status' => 'Y',
                'gender' => 'M',
                'usertype' => $usertypeId,
            ]);

            // $role = Role::create([
            //     'name' => $request->UserType. ' Admin'
            // ]);
            return response()->json([
                'status' => "true",
                'message' => 'User Type Created Successfully',
            ]);
        }
    }

    public function createUserType(Request $request)
    {
        $validation = $request->validate([
            'UserType' => 'required|unique:usertypes,name',
            'Userident' => 'required|unique:usertypes,Identifier',
        ]);
        
        $create = userTypes::create([
                'name' => $request->UserType,
                'Identifier' => $request->Userident
            ]);
        $usertypeId = $create->id;
            if($create)
            {
                $user = User::insert([
                    'name' => credential_encrypt($request->UserType . ' Admin'),
                    'username' => credential_encrypt($request->UserType . 'Admin'),
                    'email' => credential_encrypt($request->UserType . 'Admin' . '@' . 'fyntune' . '.com'),
                    'password' => bcrypt('Admin@1234'),
                    'mobile' => credential_encrypt('1234567890'),
                    'address' => credential_encrypt('Admin Address'),
                    'pincode' => credential_encrypt('123456'),
                    'status' => 'Y',
                    'gender' => 'M',
                    'usertype' => $usertypeId,
                    'is_admin' => 'Y'
                ]);
                    
                $role = Role::create([
                    'name' => $request->UserType. ' Admin',
                    'guard_name' => 'sanctum'
                ]);

                return response()->json([
                    'status' => "true",
                    'message' => 'User Type Created Successfully',
                ]);
            }
    }

    /**
     * Display the specified resource.
     */
    public function show(Request $request)
    {
        $user = Auth::user();
    
            $role_id = DB::table('model_has_roles')
            ->where('model_id', $user->id)
            ->where('model_type', 'App\Models\User')
            ->value('role_id'); 
    
        $user_access_management = UserAccessManagment::where('role_id', $role_id)->orderByDesc('id')->first();
    
        $allowedUserCreation = [];
        if ($user_access_management) {
            $decodedData = json_decode($user_access_management->data, true);
            $allowedUserCreation = $decodedData['manage_access'][0]['allowedUserCreation'] ?? [];
        }
    
        $userTypeQuery = userTypes::select('id', 'name', 'Identifier', 'is_active')
            ->where('is_active', 'Y');

            if (!empty($allowedUserCreation)) {
                $userTypeQuery->whereIn('Identifier', $allowedUserCreation);
            } elseif ($user->is_admin == 'N' || ($user->is_admin == 'Y' && $user->usertype != "1")) {
                $userTypeQuery->where('id', $user->usertype);
            }

                $userTypeList = $userTypeQuery->get();
        return response()->json([
            'status' => $userTypeList->isNotEmpty() ? "true" : "false",
            'data' => $userTypeList,
            'message' => $userTypeList->isNotEmpty() ? 'Data Found' : 'Data Not Found'
        ]);
    }
    
    public function filterUserTypeList(Request $request)
    {
        $userTypeList = userTypes::select('id', 'name', 'Identifier')
                ->where('is_visible', 'Y')
                ->whereNotIn('Identifier', ['U']) 
                ->get();

            if ($userTypeList->isNotEmpty()) { 
                return response()->json([
                    'status' => true, 
                    'data' => $userTypeList
                ]);
            } else {
                return response()->json([
                    'status' => false,
                    'data' => [],
                    'message' => 'Data Not Found'
                ]);
            }
    }
    /**
     * Show the form for editing the specified resource.
     */
    public function edit(string $id)
    {
        //
    }
   

    /**
     * Update the specified resource in storage.
     */
    public function update(UsertypeUpdtReq $request)
    {
//        $permission = config('Permission.usertype.edit');
//        if (!$this->auth->can($permission)) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }

        $id = $request->id;
        $new_val = $request->UserType;
        $activeStatus = $request->is_active;

        $update = userTypes::where('id',$id)->update([
            'name' => $new_val,
            'is_active' => $activeStatus
        ]);
        if($update)
        {
            return response()->json([
                'status' => "true",
                'message' => 'User Type Updated Successfully',
            ]);
        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => 'User Type Not Updated Successfully',
            ]);
        }

    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(Request $request)
    {
//        $permission = config('Permission.usertype.edit');
//        if(!$this->auth->can($permission))
//        {
//            return response()->json([
//                'status' => "false",
//                'message' => 'Access Denied',
//            ]);
//        }

        $id = $request->id;
        $userType = userTypes::find($id);
        if ($userType) {
            $userType->is_active = 'N';
            $userType->delete();
        }
        if($userType)
        {
            return response()->json([
                'status' => "true",
                'message' => 'User Type Deleted Successfully',
            ]);
        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => 'User Type Not Deleted Successfully',
            ]);
        }
    }

    public function show_user_type(Request $request)
    {
       $id = $request->id;
        $userTypeList = !empty($id) ?  userTypes::select('id','Identifier as user_type','name as user_table')->where('id',$id)->where('is_visible', 'Y')->get()->all() : userTypes::select('id','Identifier as user_type','name as user_table')->where('is_visible', 'Y')->get()->all();
        if(!empty($userTypeList))
        {

            return response()->json([
                'status' => "success",
                'data' => $userTypeList
            ]);
        }
        else
        {
            return response()->json([
                'status' => "error",
                'data' => "No Data Found"
            ]);
        }
    }

    public function update_usertype(Request $request)
    {
        $request->validate([
            'name' => 'required', 
        ]);
        $id = $request->id;
        $userType = userTypes::findOrFail($id);

        $userType->update([
            'name' => $request->name,
        ]);
        if ($request->reset_password == 'Y') {
            $user = User::where('usertype', $id)->where('is_admin', 'Y')
                ->join('usertypes', 'usertypes.id', '=', 'users.usertype')
                ->select('users.*') 
                ->get(); 
        
            foreach ($user as $u) {
                $u->update([
                    'password' => bcrypt('Admin@1234') // Hash password
                ]);
            }
        }
        

        if($userType)
        {
            return response()->json([
                'status' => "true",
                'message' => 'User Type Updated Successfully',
            ]);
        }
        else
        {
            return response()->json([
                'status' => "false",
                'message' => 'User Type Not Updated Successfully',
            ]);
        }


    }
}
