<?php

namespace App\Traits;

use Illuminate\Support\Facades\Auth;
use App\Models\UserAccessManagment;
use App\Models\userTypes;
use App\Models\User;

trait UserAccessTrait
{
    public function getRoleAccess()
    {
        $user = Auth::user();
        $roleId = $user->roles->pluck('id')->first();
        
        $userAccess = UserAccessManagment::where('role_id', $roleId)->first();
    
        // Initialize an empty array to store decrypted user data
        $decryptedUsers = [];
    
        // Check if $userAccess exists and contains 'manage_access'
        if ($userAccess && isset($userAccess->data)) {
            $userAccessData = json_decode($userAccess->data, true);
            
            if (isset($userAccessData['manage_access'])) {
                foreach ($userAccessData['manage_access'] as $key => $value) {
                    $identifier = $value['identifier'];
                    $usertypeIds = userTypes::whereIn('identifier', (array)$identifier)->pluck('id')->toArray();
                    $users = User::whereIn('usertype', $usertypeIds)->get();
    
                    foreach ($users as $user) {
                        $decryptedUser = [
                            'id' => $user->id,
                            'name' => credential_decrypt($user->name),
                            'middle_name' => $user->middle_name,
                            'last_name' => $user->last_name,
                            'dob' => $user->dob,
                            'license_start_date' => $user->license_start_date,
                            'license_end_date' => $user->license_end_date,
                            'email' => credential_decrypt($user->email),
                            'email_verified_at' => $user->email_verified_at,
                            'password' => $user->password,
                            'remember_token' => $user->remember_token,
                            'created_at' => $user->created_at,
                            'updated_at' => $user->updated_at,
                            'deleted_at' => $user->deleted_at,
                            'otp' => $user->otp,
                            'username' => credential_decrypt($user->username),
                            'mobile' => credential_decrypt($user->mobile),
                            'address' => credential_decrypt($user->address),
                            'pincode' => credential_decrypt($user->pincode),
                            'gender' => $user->gender,
                            'otp_expires_in' => $user->otp_expires_in,
                            'otp_expires_at' => $user->otp_expires_at,
                            'totp_secret' => credential_decrypt($user->totp_secret),
                            'status' => $user->status,
                            'otp_expiry' => $user->otp_expiry,
                            'usertype' => $user->usertype,
                            'bank_branch' => credential_decrypt($user->bank_branch),
                            'bank_city' => credential_decrypt($user->bank_city),
                            'bank_name' => credential_decrypt($user->bank_name),
                            'account_no' => credential_decrypt($user->account_no),
                            'ifsc_code' => credential_decrypt($user->ifsc_code),
                            'account_holder_name' => credential_decrypt($user->account_holder_name),
                            'nominee_first_name' => $user->nominee_first_name,
                            'nominee_last_name' => $user->nominee_last_name,
                            'nominee_middle_name' => $user->nominee_middle_name,
                            'nominee_relation' => $user->nominee_relation,
                            'nominee_dob' => $user->nominee_dob,
                            'nominee_mobile' => $user->nominee_mobile,
                            'nominee_email' => $user->nominee_email,
                            'reportingto' => $user->reportingto,
                            'employee_code' => $user->employee_code,
                            'adhar_no' => credential_decrypt($user->adhar_no),
                            'pan_no' => credential_decrypt($user->pan_no),
                            'zone_id' => $user->zone_id,
                            'Is_delegate' => $user->Is_delegate,
                            'delegate_count' => $user->delegate_count,
                            'qualification' => $user->qualification,
                            'pos_code' => $user->pos_code,
                        ];
    
                        // Add the decrypted user to the array
                        $decryptedUsers[] = $decryptedUser;
                    }
                }
            }
        }
    
        // Return the response with decrypted users data
        return response()->json([
            'status' => 200,
            'return_data' => $decryptedUsers,
            'message' => 'User data fetched successfully.',
        ]);
    }
    
}
