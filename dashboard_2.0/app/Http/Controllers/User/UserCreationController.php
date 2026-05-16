<?php

namespace App\Http\Controllers\User;

use App\Http\Controllers\Controller;
use App\Http\Requests\UserCreationRequest;
use App\Models\ZoneMasterModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use App\Models\User;
use App\Models\Role;
use App\Models\lobMaster;
use Illuminate\Support\Facades\Validator;
use App\Models\SellNow;

class UserCreationController extends Controller
{
    protected $errors = []; // Initialize errors array

    /**
     * Store a newly created resource in storage.
     */
    public function store(UserCreationRequest $request)
    {
        $validatedData = $request->all();
        DB::beginTransaction();

        $lob = lobMaster::where('is_enabled', 'Y')->pluck('id');

        $userTypeId = [
            'E' => 1,
            'P' => 2,
            'Partner' => 3,
            'b2c' => 4,
        ];

        foreach ($validatedData as $userData) {
            try {
                $user = User::create([
                    'username' => credential_encrypt($userData['mobile']),
                    'name' => credential_encrypt($userData['first_name']),
                    'middle_name' => credential_encrypt($userData['middle_name'] ?? ''),
                    'last_name' => credential_encrypt($userData['last_name'] ?? ''),
                    'gender' => $userData['gender'] ?? null,
                    'dob' => credential_encrypt($userData['dob'] ?? ''),
                    'address' => credential_encrypt($userData['address'] ?? ''),
                    'pincode' => credential_encrypt($userData['pincode'] ?? ''),
                    'mobile' => credential_encrypt($userData['mobile']),
                    'email' => credential_encrypt($userData['email']),
                    'employee_code' => $userData['employee_code'] ?? null,
                    'pos_code' => $userData['pos_code'] ?? null,
                    'adhar_no' => credential_encrypt($userData['adhar_no']),
                    'pan_no' => credential_encrypt($userData['pan_no']),
                    'license_start_date' => $userData['license_start_date'] ?? '',
                    'license_end_date' => $userData['license_end_date'] ?? '',
                    'account_holder_name' => credential_encrypt($userData['bank_account_holder_name']),
                    'account_no' => credential_encrypt($userData['bank_account_number']),
                    'ifsc_code' => credential_encrypt($userData['bank_ifsc_code']),
                    'bank_name' => credential_encrypt($userData['bank_name']),
                    'bank_city' => credential_encrypt($userData['bank_city_name']),
                    'bank_branch' => credential_encrypt($userData['branch_name']),
                    'password' => bcrypt('Admin@123'),
                    'usertype' => $userData['usertype'],
                ]);

                $lastInsertId = $user->id;

                $role = Role::where('name', $userData['role'])
                        ->where('user_type', $userTypeId[$userData['usertype']])
                        ->where('guard_name', 'sanctum') // Ensure it's assigned for sanctum
                        ->first();

                    if ($role) {
                        $user->assignRole($role->name); // Assign role using name
                    } else {
                        $this->errors[] = [
                            'errors' => "This Role Does Not Exist: " . $userData['role'],
                            'row' => $userData
                        ];
                        DB::rollBack();
                        return response()->json(['error' => $this->errors], 400);
                    }

                // Check if reporting user exists
                $reportingUser = User::where('mobile', credential_encrypt($userData['reporting_mobile_no']))
                ->first();
            
            if ($reportingUser) {
                $userType = $userTypeId[$userData['usertype']] ?? null;
            
                // Ensure userType is valid before comparing
                if ($userType != $reportingUser->usertype) {
                    if ($userData['usertype'] === 'P') {
                        $user->update([
                            'reportingto' => 3,
                            'employee_code' => $reportingUser->employee_code
                        ]);
                    } elseif ($userData['usertype'] === 'Partner') {
                        $user->update([
                            'reportingto' => 4,
                            'employee_code' => $reportingUser->employee_code
                        ]);
                    }
                } else {
                    $user->update(['reportingto' => $reportingUser->id]);
                }
            } else {
                $this->errors[] = [
                    'errors' => "Reporting User does not exist: " . $userData['reporting_mobile_no'],
                    'row' => $userData,
                ];
                DB::rollBack();
                return response()->json(['errors' => $this->errors], 422);
            }
            

                // Insert into SellNow
                foreach ($lob as $row) {
                    SellNow::create([
                        'user_id' => $lastInsertId,
                        'lob_id' => $row,
                        'created_at' => now(),
                    ]);
                }
            } catch (\Exception $e) {
                DB::rollBack();
                return response()->json(['errors' => $e->getMessage()], 500);
            }
        }

        DB::commit();
        return response()->json([
            'message' => 'Users created successfully!',
            'data' => $validatedData,
        ], 201);
    }

    public function getSellerData(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'seller_type' => 'required',
            'seller_username' => 'required',
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 422);
        }

        $userTypeId = getUserTypeIdByIdentifier($request->seller_type);

        if (empty($userTypeId)) {
            return response()->json(
                [
                    'status' => 'False',
                    'message' => 'Invalid seller type or seller type not active',
                ],
                422
            );
        }

        $user = User::select('id')
            ->where('usertype', $userTypeId)
            ->where(function ($query) use ($request) {
                $query->where('mobile', credential_encrypt($request->seller_username))
                    ->orWhere('username', credential_encrypt($request->seller_username));
            })
            ->first();

        if (empty($user)) {
            return response()->json(
                [
                    'status' => 'False',
                    'message' => 'User not found',
                ],
                422
            );
        }

        $data = DB::table('users')
            ->leftJoin('posp_ic_mappings', 'users.id', '=', 'posp_ic_mappings.user_id')
            ->where('users.id', $user->id)
            ->select('users.*', 'posp_ic_mappings.*')
            ->first();

        $zoneData = ZoneMasterModel::where('id', $data->zone_id)->pluck('office_zone')->first() ?? null;
        if ($data) {

            $formatted =  [
                "seller_id" => $user->id ?? null,
                "usertype" => $request->seller_type ?? null,
                "seller_type" => $request->seller_type ?? null,
                "source" => null,
                "seller_name" => credential_decrypt($data->name) ?? null,
                "user_name" => credential_decrypt($data->username) ?? null,
                "username" => credential_decrypt($data->username) ?? null,
                "email" => credential_decrypt($data->email) ?? null,
                "mobile" => credential_decrypt($data->mobile) ?? null,
                "aadhar_no" => credential_decrypt($data->adhar_no) ?? null,
                "pan_no" => credential_decrypt($data->pan_no) ?? null,
                "unique_number" => $data->pos_code ?? null,
                "first_name" => credential_decrypt($data->name) ?? null,
                "middle_name" => credential_decrypt($data->middle_name) ?? null,
                "last_name" => credential_decrypt($data->last_name) ?? null,
                "licence_start_date" => credential_decrypt($data->license_start_date) ?? null,
                "licence_end_date" => credential_decrypt($data->license_end_date) ?? null,
                "city" => null,
                "branch_name" => null,
                "rm_branch_code" => null,
                "region_name" => null,
                "zone_name" => $zoneData,
                "channel" => null,
                "reference_code" => $data->pos_code ?? null,
                "agent_id" => $user->id ?? null,
                "relation_acko" => null,
                "relation_aditya_birla" => null,
                "relation_aviva_life" => null,
                "relation_bajaj_life" => null,
                "relation_bharti_axa_life" => null,
                "relation_birla_sun_life" => null,
                "relation_sbi" => null,
                "relation_united_india" => null,
                "relation_hdfc_ergo" => $data->hdfc ?? null,
                "relation_tata_aig" => null,
                "relation_future_generali_life" => null,
                "agent_pos_id" => null,
                "branch_code" => null,
                "h_seller_id" => $user->id ?? null,
                "h_seller_type" => "Partner",
                "h_seller_user_name" => credential_decrypt($data->username) ?? null,
            ];

            return response()->json([
                'status' => 'true',
                "message" => "data found",
                'data' => $formatted,
            ], 200);
        } else {
            return response()->json([
                'status' => 'False',
                'message' => 'User not found',
            ], 404);
        }
    }

}


