<?php

namespace App\Http\Controllers;

use App\Http\Controllers\Master\CredentialController;
use App\Models\Credential;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Spatie\Permission\Models\Permission;

class PermissionAccessController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        //
        return view('PermissionView');
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
    public function store(Request $request)
    {
        //
        $validate = $request->validate([
            'permission' => 'required|string|max:100',
        ]);
        $permission = Permission::create(['name' =>$request->permission ]);
        if($permission)
        {
            return requestResponseMessage(['status' => 200,'message'=>'Permission Created Successfully']);
        }
        else
        {
            return requestResponseMessage(['status' => 404,'message'=>'Permission Not Created']);
        }

    }

    /**
     * Display the specified resource.
     */
    public function show(Request $request)
    {
        //

        $permissions = Permission::select('id','name')->get();
        return requestResponseMessage(['status' => 200,'data' => $permissions]);
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
    public function update(Request $request, string $id)
    {
        //
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        //
    }
    public function MapPermission(Request $request)
    {
        $validate = $request->validate([
            'permissionId' => 'required|int',
            'configId' => 'required|int',
        ]);

        $configValueSet = Credential::find($request->configId);
        $permissionName= Permission::find($request->permissionId);
        $configValueSet->credential_value = credential_encrypt($permissionName->name);
        $configValueSet->save();
        if($configValueSet)
        {
            return requestResponseMessage(['status' => 200,'message'=>'Permission Mapped With Config Successfully']);
        }
        else
        {
            return requestResponseMessage(['status' => 404,'message'=>'Permission Not Mapped With Config']);
        }
    }
    public function ListMapPermission(Request $request){
        $configGroup = DB::table('configmaster')
        ->select('id')
        ->where('key', '=', 'Permissions')
        ->first();
        if ($configGroup) {
            // Fetch credentials and decrypt the credential_value
            $configValueSet = Credential::select('credential_value as value', 'credential_key as key')
                ->where('configuration', $configGroup->id)
                ->get()
                ->map(function($credential) {
                    // Decrypt the credential_value
                    $credential->value = credential_decrypt($credential->value); // Assuming credential_decrypt is your custom function
                    return $credential;
                });
        
            // Return the response with the decrypted data
            return requestResponseMessage([
                'status' => 200,
                'data' => $configValueSet
            ]);
        } else {
            // Handle case when $configGroup is not found
            return requestResponseMessage([
                'status' => 404,
                'message' => 'Configuration group not found.'
            ]);
        }  
    }
}