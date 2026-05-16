<?php

namespace App\Http\Controllers;

use App\Models\User;
use App\Models\Customer;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;

class ProfileController extends Controller
{
    public function getData()
    {
        $user = Auth::user();

        $data = $user->usertype == "5"
        ? Customer::find($user->id)
        : User::find($user->id);
    
        $results = [
            'id' => $data->id,
            'name' => credential_decrypt($data->name),
            'middle_name' => credential_decrypt($data->middle_name),
            'last_name' => credential_decrypt($data->last_name),
            'username' => credential_decrypt($data->username),
            'email' => credential_decrypt($data->email),
            'mobile' => credential_decrypt($data->mobile),
            'account_holder_name' => credential_decrypt($data->account_holder_name),
            'ifsc_code' => credential_decrypt($data->ifsc_code),
            'account_no' => credential_decrypt($data->account_no),
            'bank_name' => credential_decrypt($data->bank_name),
            'bank_city' => credential_decrypt($data->bank_city),
            'bank_branch' => credential_decrypt($data->bank_branch)
        ];

        if ($data) {
            return ([
                'status' => 200,
                'message' => 'success',
                'data' => $results
            ]);
        } else {
            return ([
                'status' => 404,
                'message' => 'Data Not Found'
            ]);
        }
    }

    public function updateProfile(Request $request)
    {
        $user = Auth::user();
        
        if (!empty($request)) {
            $model = $user->usertype != "5" ? User::class : Customer::class;

            $data = $model::where('id', $request->id)->update([
                'name' => credential_encrypt($request->name),
                'middle_name' => credential_encrypt($request->middle_name),
                'last_name' => credential_encrypt($request->last_name),
                'email' => credential_encrypt($request->email),
                'mobile' => credential_encrypt($request->mobile),
                'account_holder_name' => credential_encrypt($request->account_holder_name),
                'ifsc_code' => credential_encrypt($request->ifsc_code),
                'account_no' => credential_encrypt($request->account_no),
                'bank_name' => credential_encrypt($request->bank_name),
                'bank_city' => credential_encrypt($request->bank_city),
                'bank_branch' => credential_encrypt($request->bank_branch)
            ]);


            if ($data) {
                return ([
                    "status" => 200,
                    "message" => "Data Updated Successfully"
                ]);
            } else {
                return ([
                    'status' => 404,
                    'message' => 'Data Not Found'
                ]);
            }
        } else {
            return ([
                'status' => 500,
                'message' => 'Data Not Found'
            ]);
        }
    }
}
