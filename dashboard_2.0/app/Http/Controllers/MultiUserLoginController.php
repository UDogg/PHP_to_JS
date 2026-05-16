<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\userTypes;
use App\Models\UserMapping;
use App\Models\User;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Auth;

class MultiUserLoginController extends Controller
{
    public function switchUser(Request $request) 
    {
        $request->validate([
            'mobile' => 'required|string',
            'user_id' => 'required|integer',
            'user_type' => 'required|integer',
        ]);
        
        $mobile = credential_decrypt($request->mobile);
        $userId = $request->user_id; 
        $userData = User::where('mobile', credential_encrypt($mobile))->get()->pluck('id')->toArray();
        if (empty($userData)) {
            return response()->json(['status' => 404, 'message' => 'No user found with the provided mobile'], 404);
        }else{

            $usersWithSameMobileAndType = UserMapping::where('user_id', $userData)
                                        ->get();
            $tokens = [];
            $allUserIds = []; 
            
            foreach ($usersWithSameMobileAndType as $user) {
                $allUserIds[] = $user->id;
                if ($user->user_type === $request->user_type) {
                    $token = generateTokenAll($user);
                    $tokens[] = [
                        'user_id' => $user->id,
                        'token' => $token,
                    ];
                }
            }
            return response()->json([
                'status' => 200,
                'message' => 'Multi User Logged In',
                'return_data' => [
                    'user_ids' => $allUserIds,
                    'tokens' => $tokens,
                ],
            ]);
                
            }
    }

    public function newSwitchUser(Request $request)
    {
        $userId = $request->user_id;
        $userType = $request->user_type;

        $user = User::find($userId);

        if (!$user) {
            return response()->json([
                'status' => 403,
                'message' => "User not found",
            ], 403);
        }

        // Map user type string to user type ID
        $userTypeMap = [
            'Employee' => '1',
            'POS' => '2',
            'Partner' => '3',
            'B2C' => '4',
        ];

        $finalUserType = $userTypeMap[$userType] ?? null;

        if (!$finalUserType) {
            return response()->json([
                'status' => 400,
                'message' => "Invalid user type",
            ], 400);
        }

        // If already the same user type, just regenerate token
        if ($user->usertype == $finalUserType) {
            $request->user()->tokens()->delete(); // Revoke current tokens
            $userToken = generateTokenAll($user);

        } else {
            // Check if user has mapping for requested user type
            $mappedUser = UserMapping::where('user_id', $userId)
                ->where('user_type', $finalUserType)
                ->first();

            if (!$mappedUser) {
                return response()->json([
                    'status' => 403,
                    'message' => "User does not have access to $userType",
                ], 403);
            }

            $user->usertype = $finalUserType;
            $request->user()->tokens()->delete(); // Revoke current tokens

            $metadata = [
                "usertype:$finalUserType",
                "userRole:$mappedUser->role_id",
                "switch:true"
            ];

            $userToken = generateTokenAll($user,$metadata);

        }

        return response()->json([
            'status' => 200,
            'token_type' => 'Bearer',
            'access_token' => $userToken,
            'usertype' => $userType,
            'usertype_id' => $user->usertype,
            'frontend_url' => "$userType/dashboard",
            'message' => 'Login successfully',
        ]);
    }

}
