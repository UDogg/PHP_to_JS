<?php

namespace App\Http\Controllers\User;

use App\Http\Controllers\Controller;
use App\Models\User;
use App\Models\UserAccessManagment;
use App\Models\userTypes;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;

class UserAccessManagementController extends Controller
{
    public function store(Request $request){
        $user_access_management = UserAccessManagment::where('role_id', $request->role_id)->where('user_id', $request->user_id)
        ->whereJsonContains('data->manage_access', ['menu_id' => $request->menu_id])
        ->first();
        if($user_access_management){ 
            $userAccessData = json_decode($user_access_management->data, true)['manage_access'] ?? [];
            $requestData = $request->data['manage_access'] ?? [];
            $userAccessDataAssoc = [];
            foreach ($userAccessData as $access) {
                $userAccessDataAssoc[$access['menu_id']] = $access['identifier'];
            }
            foreach ($requestData as $access) {
                $menuId = $access['menu_id'];
                $newIdentifiers = $access['identifier'];
                $userAccessDataAssoc[$menuId] = $newIdentifiers;
            }
            $updatedAccessData = [];
            foreach ($userAccessDataAssoc as $menuId => $identifiers) {
                $updatedAccessData[] = [
                    'menu_id' => $menuId,
                    'identifier' => $identifiers,
                ];
            }

            $allowedUsers = $request->allowedUserCreation;

            // Add a new key-value pair to the array
            $updatedAccessData[count($updatedAccessData) - 1]['allowedUserCreation'] = $allowedUsers;

            $user_access_management->data = json_encode(['manage_access' => $updatedAccessData]);
            $user_access_management->save();
            
            return response()->json(['status' => '200', 'return_data'=>$user_access_management, 'message' => 'Access data updated successfully']);
        }else{
            $rules = [
                'role_id' => 'required',
                'user_id' => 'required',
                'data' => 'required',
            ];
            $validator = Validator::make( $request->all(), $rules);
            if ($validator->fails()) {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'validations fails',
                            'errors' => $validator->errors()
                        ],
                        500
                    );
            }else{

                $allowedUsers = $request->allowedUserCreation;
                  $jsonData = $request->data;

                  // Adding the `allowedUserCreation` key and its value
                  $jsonData["manage_access"][0]["allowedUserCreation"] = $allowedUsers;

                $user = Auth::user();
                $user_type_id = $user->usertype;
                $user_type = userTypes::where('id', $user_type_id)->select('Identifier')->first();
                $user_type = $user_type->Identifier;
                $user_access_managment = new UserAccessManagment();
                $user_access_managment->role_id = $request->role_id;
                $user_access_managment->user_id = $request->user_id;
                $user_access_managment->type = $user_type;
                $user_access_managment->data = json_encode($jsonData);
                $user_access_managment->save();
                if ($user_access_managment->save()==true) {
                    return response()->json(
                        [
                            'status' => 200,
                            'return_data' => $user_access_managment,
                            'message' => 'User Access Management Created Successfully.',
                        ],
                        200
                    );
                } else {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'Error While Creating User Access Management.',
                        ],
                        500 );
                    }
            }   
        }       
    }
    public function list(Request $request)
    {
        // $menuId = $request->input('menu_id');
        // $userAccessData = UserAccessManagment::whereJsonContains('data->manage_access', ['menu_id' => (int)$menuId])->get();
        $roleId = $request->input('role_id'); 
        $userAccessData = UserAccessManagment::where('role_id', $roleId)->get();  
        if ($userAccessData->isNotEmpty()) {
            $userAccessDataArray = $userAccessData->map(function ($item) {
                $itemArray = $item->toArray();
                $itemArray['data'] = json_decode($item->data, true);
                return $itemArray;
            });

            return response()->json([
                'success' => 200,
                'return_data' => $userAccessDataArray,
                'message' => 'Data fetched successfully.',
            ], 200);
        } else {
            return response()->json([
                'success' => 500,
                'return_data' => [],
                'message' => 'No data found for the given menu.',
            ], 500);
        }
    }
    
}

