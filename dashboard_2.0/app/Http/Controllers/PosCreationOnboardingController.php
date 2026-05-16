<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\Hash;
use App\Models\User;
use App\Models\UserMapping;
use App\Models\QualificationMaster;
use Illuminate\Support\Carbon;

class PosCreationOnboardingController extends Controller
{
    public function PosCreationOnboarding(Request $request)
    {
        $input = $request->json()->all();
   

        if (empty($input)) {
            return response()->json(["status" => false, "message" => "Invalid arguments passed"]);
        }

        $allKeys = [
            'agent_name',
            'user_name',
            'aadhar_no',
            'gender',
            'mobile',
            'email',
            'date_of_birth',
            'marital_status',
            'pan_no',
            'educational_qualification',
            'address',
            'city',
            'state',
            'pincode',
            'bank_name',
            'bank_account_no',
            'ifsc_code',
            'bank_branch_name',
            'training_start_date',
            'training_end_date',
            'rm_name',
            'rm_number',
            'first_name',
            'middle_name',
            'last_name',
            'licence_start_date',
            'licence_end_date'
        ];

        $requiredFields = ['agent_name', 'user_name', 'mobile', 'email'];

        $missingFields = [];
        foreach ($allKeys as $key) {
            if (!array_key_exists($key, $input) || (in_array($key, $requiredFields) && empty($input[$key]))) {
                $missingFields[] = $key;
            }
        }

        if (!empty($missingFields)) {
            return response()->json(["status" => false, "message" => "Missing or empty fields", "fields" => $missingFields]);
        }

        // Check and Insert RM if not exists
        if (!empty($input['rm_number'])) {
            $rm = User::where('mobile', credential_encrypt($input['rm_number']))->where('usertype', '1')->first();
          
            if (!$rm) {
                $rm = User::create([
                    'name' => credential_encrypt($input['rm_name']),
                    'username' => credential_encrypt($input['rm_number']),
                    'password' => credential_encrypt('Admin@123'),
                    'mobile' => credential_encrypt($input['rm_number']),
                    'email' => credential_encrypt($input['rm_email'] ?? null),
                    'employee_code' => $input['rm_number'],
                    'reportingto' => 2,
                    'status' => 'Y',
                    'usertype' => 1,
                    'created_at' => now()
                ]);
            }
            $reportingTo   = $rm->id;
            $employeeCode  = $rm->employee_code;
        }

        $qualificationId = QualificationMaster::whereRaw('LOWER(qualification_name) = ?', [strtolower(trim($input['educational_qualification']))])
        ->where('status', 'Y')
        ->value('qualification_master_id');
        
    
        $commonData = [
            'name' => credential_encrypt($input['first_name'] ?? null),
            'middle_name' => credential_encrypt($input['middle_name'] ?? null),
            'last_name' => credential_encrypt($input['last_name'] ?? null),
            'dob' => credential_encrypt($input['date_of_birth'] ?? null),
            'license_start_date' => credential_encrypt($input['licence_start_date'] ?? null),
            'license_end_date' => credential_encrypt($input['licence_end_date'] ?? null),
            'email' => credential_encrypt($input['email']),
            'password' => credential_encrypt('Admin@123'),
            'username' => credential_encrypt($input['mobile']),
            'mobile' => credential_encrypt($input['mobile']),
            'address' => credential_encrypt($input['address']),
            'pincode' => credential_encrypt($input['pincode']),
            'gender' => strtolower($input['gender']) === 'male' ? 'M' : 'F',
            'status' => 'Y',
            'usertype' => 2,
            'bank_branch' => credential_encrypt($input['bank_branch_name']),
            'bank_city' => credential_encrypt($input['city']),
            'bank_name' => credential_encrypt($input['bank_name']),
            'account_no' => credential_encrypt($input['bank_account_no']),
            'ifsc_code' => credential_encrypt($input['ifsc_code']),
            'account_holder_name' => credential_encrypt($input['first_name']),
            'reportingto' => $reportingTo ?? null,
            'employee_code' => $employeeCode ?? null,
            'adhar_no' => credential_encrypt($input['aadhar_no']),
            'pan_no' => credential_encrypt($input['pan_no']),
            'zone_id' => 2,
            'delegate_count' => 0,
            'qualification' => $qualificationId,
            'pos_code' => $input['user_name'],
            'is_admin' => 'N',
            'pan_link_status' => 0,
            'updated_at' => now()
        ];

        if(!empty($input['supervisoer_mobile'])){
            $commonData['child_pos'] = 0;
        }   
       
        $encryptedMobile = credential_encrypt($input['mobile']);

        $user = User::where('mobile', $encryptedMobile)->first(); 

        if (!$user) {
            $user = User::create($commonData);

            $role = DB::table('roles')->where('name', 'Posp')->where('user_type', 2)->first();
            if ($role) {
                DB::table('model_has_roles')->insert([
                    'role_id' => $role->id,
                    'model_type' => 'App\Models\User',
                    'model_id' => $user->id
                ]);
            }

            if (!empty($input['products'])) {
                $productArray = array_map('trim', explode(',', strtolower($input['products'])));
                $lobIds = DB::table('lob_master')
                    ->where('is_enabled', 'Y')
                    ->whereIn(DB::raw('LOWER(lob)'), $productArray)
                    ->pluck('id')
                    ->toArray();
            } else {
                $lobIds = DB::table('lob_master')
                    ->where('is_enabled', 'Y')
                    ->pluck('id')
                    ->toArray();
            }

            foreach ($lobIds as $lobId) {
                DB::table('user_lob_relation')->insert([
                    'user_id' => $user->id,
                    'lob_id' => $lobId,
                    'created_at' => Carbon::now(),
                    'updated_at' => null,
                ]);
            }

            return response()->json(["status" => true, "message" => "Successfully Inserted"]);
        } else {
            
            $mappingExists = DB::table('user_mappings')
                ->where('user_id', $user->id)
                ->where('user_type', 2)
                ->exists();

            if ($mappingExists) {
                return response()->json(["status" => false, "message" => "User is already created with this mobile number"]);
            }

            
            DB::table('user_mappings')->insert([
                'user_id' => $user->id,
                'user_type' => 2,
                'role_id' => $role->id ?? null,
                'reportingto' => $reportingTo ?? null,
                'employee_code' => $employeeCode ?? null,
                'created_at' => Carbon::now(),
            ]);

            return response()->json(["status" => true, "message" => "User successfully created "]);
        }
    }


    public function statusChange(Request $request)
    {
         $input = $request->all();

        if (empty(isset($input['mobile']))) {
            return response()->json([
                'status' => false,
                'message' => 'Please check input parameters'
            ]);
        }

        $encryptedMobile = credential_encrypt($input['mobile']);

        $user = User::where('mobile', $encryptedMobile)->first(); 

        if (!$user) {
            return response()->json(['status' => false, 'message' => 'No pos found']);
        }

        if ($user->usertype == 2) {
            return response()->json(['status' => true, 'message' => 'POS found']);
        }

        $mappedPos = UserMapping::where('user_id', $user->id)
            ->where('user_type', 2)
            ->exists();

        if ($mappedPos) {
            return response()->json(['status' => true, 'message' => 'POS found']);
        } else {
            return response()->json(['status' => false, 'message' => 'No pos found']);
        }
        
    }
}
