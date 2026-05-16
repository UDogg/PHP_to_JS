<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Log;

class DashboardUserMigrationController extends Controller
{
    public function migrateCustomers(Request $request)
    {
        $table = $request->input('tabel');
        $otherApi = $request->input('other_api');
        $limit = $request->input('limit');

        // $username = $request->input('username');
        // $password = $request->input('password');

        // if (!$username || !$password) {
        //     return response()->json(['message' => 'Username or password missing for Basic Auth.'], 400);
        // }

        // $basicAuth = base64_encode("$username:$password");

    
        if (!$table || !$otherApi) {
            return response()->json(['message' => 'Missing required parameters.'], 400);
        }
    
        // Fetch users with null or pending status
        $query = DB::table($table)
            ->where(function ($q) {
                $q->whereNull('migration_status')
                  ->orWhere('migration_status', 'pending');
            });
    
        if ($limit) {
            $query->limit((int)$limit);
        }
    
        $oldUsers = $query->get();
    
        if ($oldUsers->isEmpty()) {
            return response()->json(['message' => 'No users left to migrate.']);
        }
    
        $migratedCount = 0;
        $failed = [];
        $response_data = [];


        foreach ($oldUsers as $oldUser) {
            
            // Check if user already exists
            $existingUser = DB::table('customers')->where('mobile', credential_encrypt($oldUser->mobile_no))->where('usertype',5)->first();
    
            // dd($existingUser);
            if ($existingUser) {
                $newUserId = $existingUser->id;
            } else {
                // Encrypt sensitive data
                $encryptedEmail = credential_encrypt($oldUser->email);
                $encryptedMobile = credential_encrypt($oldUser->mobile_no);
                $encryptedName = credential_encrypt($oldUser->first_name);
                $encryptedfirst_name = credential_encrypt($oldUser->first_name);
                $encryptedlast_name = credential_encrypt($oldUser->last_name);
                $encrypteddob = credential_encrypt($oldUser->dob);
    
                // Insert into new users table
                $newUserId = DB::table('customers')->insertGetId([
                    'name' => $encryptedfirst_name,
                    'first_name' => $encryptedfirst_name,
                    'last_name' => $encryptedlast_name,
                    'gender' => credential_encrypt($oldUser->gender),
                    // 'dob' => $encrypteddob,
                    'email' => $encryptedEmail,
                    'mobile' => $encryptedMobile,
                    'username' => $encryptedMobile,
                    // 'password' => Hash::make('pass@123'),
                    'password'          => '$2y$12$DTdw8u4HYw2zmHlzNnehZu59zvIOVVE8MmyixE4UVzcyxJvMN2yAq',
                    'old_user_id' => $oldUser->user_id,
                    'role_id' => 9,
                    'usertype' => 5,
                    'created_at' => now(),
                    'updated_at' => now(),
                ]);

                $CustomerAssignRole = DB::table('model_has_roles')->insert([
                    'role_id' => 9,
                    'model_type' => 'App\Models\Customer',
                    'model_id' => $newUserId
                ]);
            }
    
            //     $tokenResponse = Http::withHeaders([
            //         'Content-Type' => 'application/json',
            //         'Authorization' => 'Basic ' . $basicAuth,
            //         ])->post('https://www.karoinsure.in/ma/api/tokenGeneration', [
            //         'api_endpoint' => $otherApi,
            //     ]);

            //     if (!$tokenResponse->successful() || !$tokenResponse['status']) {
            //         return response()->json([
            //             'message' => 'Failed to generate token',
            //             'error' => $tokenResponse->json(),
            //         ], 500);
            //     }

            //     $token = $tokenResponse['token'];
            // // Call external API
            // $response = Http::withHeaders([
            //     'Content-Type' => 'application/json',
            //     'validation' => $token,
            // ])->post($otherApi, [
            //     'seller_type' => 'U',
            //     'user_id' => $oldUser->user_id,
            //     'new_data' => [
            //         'user_id' => $newUserId,
            //     ],
            // ]);
    
            // $response_data[]=[$response->body()];
            // $request_data[]=[
            //     'seller_type' => 'U',
            //     'user_id' => $oldUser->user_id,
            //     'new_data' => [
            //         'user_id' => $newUserId,
            //     ],
            // ];
            // if ($response->successful()) {
            //     // Update status
                DB::table($table)
                    ->where('user_id', $oldUser->user_id)
                    ->update(['migration_status' => 'migrated']);
    
                $migratedCount++;

               

                //add lob for other users
            // } else {
            //     // Mark as pending for retry
            //     DB::table($table)
            //         ->where('user_id', $oldUser->user_id)
            //         ->update(['migration_status' => 'pending']);
    
            //     $failed[] = [
            //         'old_user_id' => $oldUser->user_id,
            //         'error' => $response->body(),
            //     ];
            // }
        }
    
        return response()->json([
            'status' => true,
            'message' => 'Migration completed.',
            'migrated_count' => $migratedCount,
            // 'response_data' => $response_data,
            // 'request_data' => $request_data,
            'failed' => $failed,
        ]);
    }
    public function migrate(Request $request)
    {
        $table = $request->input('tabel');
        $otherApi = $request->input('other_api');
        $limit = $request->input('limit');

        $username = $request->input('username');
        $password = $request->input('password');

        if (!$username || !$password) {
            return response()->json(['message' => 'Username or password missing for Basic Auth.'], 400);
        }

        $basicAuth = base64_encode("$username:$password");

    
        if (!$table || !$otherApi) {
            return response()->json(['message' => 'Missing required parameters.'], 400);
        }
    
        // Fetch users with null or pending status
        $query = DB::table($table)
            ->where(function ($q) {
                $q->whereNull('migration_status')
                  ->orWhere('migration_status', 'pending');
            });
    
        if ($limit) {
            $query->limit((int)$limit);
        }
    
        $oldUsers = $query->get();
    
        if ($oldUsers->isEmpty()) {
            return response()->json(['message' => 'No users left to migrate.']);
        }
    
        $migratedCount = 0;
        $failed = [];
        $response_data = [];


        foreach ($oldUsers as $oldUser) {
            // Check if user already exists
            $existingUser = DB::table('customers')->where('mobile', credential_encrypt($oldUser->mobile_no))->where('usertype',5)->first();
    
            // dd($existingUser);
            if ($existingUser) {
                $newUserId = $existingUser->id;
            } else {
                // Encrypt sensitive data
                $encryptedEmail = credential_encrypt($oldUser->email);
                $encryptedMobile = credential_encrypt($oldUser->mobile);
                $encryptedName = credential_encrypt($oldUser->first_name);
                $encryptedfirst_name = credential_encrypt($oldUser->first_name);
                $encryptedlast_name = credential_encrypt($oldUser->last_name);
                $encrypteddob = credential_encrypt($oldUser->dob);
    
                // Insert into new users table
                $newUserId = DB::table('users')->insertGetId([
                    'name' => $encryptedfirst_name,
                    'last_name' => $encryptedlast_name,
                    'dob' => $encrypteddob,
                    'email' => $encryptedEmail,
                    'mobile' => $encryptedMobile,
                    'username' => $encryptedUsername,
                    'password' => Hash::make('pass@123'),
                    'old_user_id' => $oldUser->id,
                    'role_id' => 9,
                    'usertype' => 5,
                    'created_at' => now(),
                    'updated_at' => now(),
                ]);
            }
    
            //     $tokenResponse = Http::withHeaders([
            //         'Content-Type' => 'application/json',
            //         'Authorization' => 'Basic ' . $basicAuth,
            //         ])->post('https://www.karoinsure.in/ma/api/tokenGeneration', [
            //         'api_endpoint' => $otherApi,
            //     ]);

            //     if (!$tokenResponse->successful() || !$tokenResponse['status']) {
            //         return response()->json([
            //             'message' => 'Failed to generate token',
            //             'error' => $tokenResponse->json(),
            //         ], 500);
            //     }

            //     $token = $tokenResponse['token'];
            // // Call external API
            // $response = Http::withHeaders([
            //     'Content-Type' => 'application/json',
            //     'validation' => $token,
            // ])->post($otherApi, [
            //     'seller_type' => 'U',
            //     'user_id' => $oldUser->user_id,
            //     'new_data' => [
            //         'user_id' => $newUserId,
            //     ],
            // ]);
    
            // $response_data[]=[$response->body()];
            // $request_data[]=[
            //     'seller_type' => 'U',
            //     'user_id' => $oldUser->user_id,
            //     'new_data' => [
            //         'user_id' => $newUserId,
            //     ],
            // ];
            // if ($response->successful()) {
            //     // Update status
                DB::table($table)
                    ->where('user_id', $oldUser->user_id)
                    ->update(['migration_status' => 'migrated']);
    
                $migratedCount++;

                $CustomerAssignRole = DB::table('model_has_roles')->insert([
                    'role_id' => 9,
                    'model_type' => 'App\Models\Customer',
                    'model_id' => $newUserId->id
                ]);

                //add lob for other users
            // } else {
            //     // Mark as pending for retry
            //     DB::table($table)
            //         ->where('user_id', $oldUser->user_id)
            //         ->update(['migration_status' => 'pending']);
    
            //     $failed[] = [
            //         'old_user_id' => $oldUser->user_id,
            //         'error' => $response->body(),
            //     ];
            // }
        }
    
        return response()->json([
            'status' => true,
            'message' => 'Migration completed.',
            'migrated_count' => $migratedCount,
            'response_data' => $response_data,
            'request_data' => $request_data,
            'failed' => $failed,
        ]);
    }
    public function migrateCustomersOld(Request $request)
    {
        $limit = $request->input('limit');
        $username = $request->input('username');
        $password = $request->input('password');
        $otherApi = $request->input('other_api');

        if (!$username || !$password) {
            return response()->json(['message' => 'Username or password missing for Basic Auth.'], 400);
        }

        $basicAuth = base64_encode("$username:$password");

        // Query active customers from `users` table
        $query = DB::table('users')
            ->where('usertype', 5)
            ->where('status', 'Y')
            ->where(function ($q) {
                $q->whereNull('migration_status')->orWhere('migration_status', 'pending');
            });

        if ($limit) {
            $query->limit((int) $limit);
        }

        $oldUsers = $query->get();
        if ($oldUsers->isEmpty()) {
            return response()->json(['message' => 'No users left to migrate.']);
        }

        $migrated = 0;
        $failed = [];
        $response_data = [];
        $request_data = [];

        foreach ($oldUsers as $user) {
            $exists = DB::table('customers')->where('user_id', $user->id)->first();

            if (!$exists) {
                // Encrypt data
                $encryptedData = [
                    'first_name' => credential_encrypt($user->name),
                    'last_name' => credential_encrypt($user->last_name),
                    'email' => credential_encrypt($user->email),
                    'mobile' => credential_encrypt($user->mobile),
                    'dob' => credential_encrypt($user->dob),
                    'user_id' => $user->id,
                    'username' => credential_encrypt($user->mobile),
                    'password' => $user->password, // Keep existing hashed password
                    'created_at' => now(),
                    'updated_at' => now(),
                ];

                // Insert into customers table
                DB::table('customers')->insert($encryptedData);
            }

            // External API sync
            if ($otherApi) {
                $tokenRes = Http::withHeaders([
                    'Content-Type' => 'application/json',
                    'Authorization' => 'Basic ' . $basicAuth,
                ])->post('https://www.karoinsure.in/ma/api/tokenGeneration', [
                    'api_endpoint' => $otherApi,
                ]);

                if (!$tokenRes->successful() || !$tokenRes['status']) {
                    $failed[] = ['user_id' => $user->id, 'error' => 'Token generation failed'];
                    continue;
                }

                $token = $tokenRes['token'];
                $apiResponse = Http::withHeaders([
                    'Content-Type' => 'application/json',
                    'validation' => $token,
                ])->post($otherApi, [
                    'seller_type' => 'U',
                    'user_id' => $user->id,
                    'new_data' => ['user_id' => $user->id],
                ]);

                $request_data[] = [
                    'seller_type' => 'U',
                    'user_id' => $user->id,
                    'new_data' => ['user_id' => $user->id],
                ];
                $response_data[] = $apiResponse->body();

                if (!$apiResponse->successful()) {
                    $failed[] = ['user_id' => $user->id, 'error' => $apiResponse->body()];
                    continue;
                }
            }

            // Mark original record as migrated
            DB::table('users')->where('id', $user->id)->update(['migration_status' => 'migrated']);
            $migrated++;
        }

        return response()->json([
            'status' => true,
            'migrated_count' => $migrated,
            'response_data' => $response_data,
            'request_data' => $request_data,
            'failed' => $failed,
        ]);
    }

    public function migrateEmployee(Request $request)
    {
        
        $table = $request->input('table');
        $otherApi = $request->input('other_api');
        $limit = $request->input('limit');
        $type = $request->input('type');
        $healthApi = $request->input('other_api_health');

        if (!$table) {
            return response()->json(['message' => 'Missing required parameters.'], 400);
        }
        // try{

        // dynamic field mapping based on table
        switch ($table) {
            case 'bcl_old_agents':
                $nameColumn = 'agent_name';
                $idColumn = 'agent_id';
                $userType = 2;
                $role_id=5;
                $supervisorColumn = 'supervisoer_mobile'; 
                break;
            case 'bcl_old_employees':
                $nameColumn = 'employee_name';
                $idColumn = 'employee_id';
                $userType = 1;
                $role_id=3;
                $supervisorColumn = 'parent'; 
                break;
            case 'bcl_old_partners':
            default:
                $nameColumn = 'partner_name';
                $idColumn = 'partner_id';
                $userType = 3;
                $role_id=7;
                $supervisorColumn = 'supervisoer_mobile';
                break;
        }
        
        $query = DB::table($table);
        
        switch ($type) {
            case 'creation':
                $query->where('creation_status', 0);
                $query->where('mapping_role', '!=', 0);
                break;
            case 'mapping':
                $query->where('mapping_status', 0);
                $query->where('creation_status', 1);
                // $query->where('mapping_supervisoer_id', '!=', 0);
                break;
            case 'motor_mapping':
                $query->where('motor_mapping_status', 0);
                $query->where('mapping_status', 1);
                $query->where('creation_status', 1);
                break;
            case 'health_mapping':
                $query->where('health_mapping_status', 0);
                $query->where('mapping_status', 1);
                $query->where('creation_status', 1);
                break;
        }
        
        if ($limit) {
            $query->limit((int)$limit);
        }

        $oldUsers = $query->get();

        if ($oldUsers->isEmpty()) {
            return response()->json(['message' => 'No users left to migrate.']);
        }

        $migratedCount = 0;
        $failed = [];
        $motorToken = null;

        if ($type === 'motor_mapping') {
            $basicAuth = base64_encode("webservice1@fyntune.com:Testing@1234");
            $tokenResponse = Http::withHeaders([
                'Content-Type' => 'application/json',
                'Authorization' => 'Basic ' . $basicAuth,
            ])->post('https://uatmotorapi.heroinsurance.com/api/tokenGeneration', [
                'api_endpoint' => $otherApi,
            ]);

            if ($tokenResponse->successful() && $tokenResponse['status']) {
                $motorToken = $tokenResponse['token'];
            } else {
                Log::channel('single')->error("Motor token generation failed", ['response' => $tokenResponse->json()]);
                return response()->json([
                    'message' => 'Failed to generate motor token',
                    'error' => $tokenResponse->json(),
                ], 500);
            }
        }

        foreach ($oldUsers as $oldUser) {
            $encryptedUsername = credential_encrypt($oldUser->user_name);
            $existingUser = DB::table('users')->where('user_name', $encryptedUsername)->first();

            if ($type === 'creation') {
                if ($existingUser) {
                    $newUserId = $existingUser->id;
                   $sameUsertypeExits= DB::table('users')->where('id', $existingUser->id)->where('usertype', '3')->first();

                   if ($sameUsertypeExits) {
                    $newUserId = $existingUser->id;
                   } else {
                    $sameUsertypeExitsmapping= DB::table('user_mappings')->where('user_id', $existingUser->id)->where('user_type', '3')->first();

                    if (!$sameUsertypeExitsmapping) {
                        $insertMappingUser = DB::table('user_mappings')->insert([
                        
                            'user_id'   => $newUserId,
                            'user_type'      => $userType,
                            'status'        => $oldUser->status == 'Active' ? 'Y' : 'N',
                            'role_id'   => $oldUser->mapping_role,
                            'employee_code' => $oldUser->employee_code,
                            'old_user_id' => $oldUser->$idColumn,
                            'reportingto' => $role_id,
                            'created_at'    => now(),
                            'updated_at'    => now(),
                        ]);

                        DB::table($table)->where('mobile', $oldUser->mobile)->update(['creation_status' => 1]);
                        // DB::table('users')->where('id', $newUserId)->update(['old_user_id' => $oldUser->employee_id]);

                        $existingUserModel = DB::table('model_has_roles')->where('model_id', $newUserId)->where('role_id', $oldUser->mapping_role)->exists();
                        if(!$existingUserModel){
                            DB::table('model_has_roles')->insert([
                                'role_id'    => $oldUser->mapping_role,
                                'model_type' => 'App\Models\User',
                                'model_id'   => $newUserId
                            ]);
                        }
                        Log::info("New user created with ID: $newUserId");

                        Log::info("Assigned roles and lob to role ID: {$oldUser->mapping_role}");

                        $lob_ids = [1, 2, 3, 4, 5, 6, 8];
                        foreach ($lob_ids as $lob_id) {
                            DB::table('user_lob_relation')->insert([
                                'user_id' => $newUserId,
                                'lob_id'  => $lob_id,
                            ]);
                        }
                }
                    }
                } else {
                    //dynamic name field
                    $fullName = trim($oldUser->$nameColumn);
                    $nameParts = preg_split('/\s+/', $fullName);
                    $firstName = $nameParts[0] ?? '';
                    $middleName = count($nameParts) === 3 ? $nameParts[1] : '';
                    $lastName = end($nameParts);
                    if (count($nameParts) === 2) {
                        $lastName = $nameParts[1];
                    }

                    ////employee and employee/////
                    $newUserId = DB::table('users')->insertGetId([
                        'name'          => credential_encrypt($firstName),
                        'middle_name'   => credential_encrypt($middleName),
                        'last_name'     => credential_encrypt($lastName),
                        'employee_code' => $oldUser->employee_code,
                        'username'      => $encryptedUsername ?? credential_encrypt('NA'),
                        'password'      => Hash::make('Admin@123'),
                        // 'password'          => '$2y$12$DTdw8u4HYw2zmHlzNnehZu59zvIOVVE8MmyixE4UVzcyxJvMN2yAq',
                        'mobile'        => $encryptedMobile ?? credential_encrypt('NA'),
                        'email'         => $oldUser->email ? credential_encrypt($oldUser->email) : '',
                        'old_user_id'   => $oldUser->$idColumn, 
                        'status'        => $oldUser->status == 'Active' ? 'Y' : 'N',
                        'is_admin'        => $oldUser->level == 1 ? 'Y' : 'N',
                        'usertype'      =>  $userType,
                        'reportingto' => $role_id,
                        'created_at'    => now(),
                        'updated_at'    => now(),
                    ]);


                    // $newUserId = DB::table('users')->insertGetId([
                    //     'name'              => credential_encrypt($oldUser->first_name ?? $firstName),
                    //     'middle_name'       => credential_encrypt($oldUser->middle_name ?? $middleName),
                    //     'last_name'         => credential_encrypt($oldUser->last_name ?? $lastName),
                    //     'dob'               => credential_encrypt($oldUser->date_of_birth),
                    //     'license_start_date'=> credential_encrypt($oldUser->licence_start_date),
                    //     'license_end_date'  => credential_encrypt($oldUser->licence_end_date),
                    //     'email'             => credential_encrypt($oldUser->email),
                    //     // 'password'          => Hash::make('pass@123'),
                    //     'password'          => '$2y$12$DTdw8u4HYw2zmHlzNnehZu59zvIOVVE8MmyixE4UVzcyxJvMN2yAq',
                    //     'username'          => credential_encrypt($oldUser->mobile),
                    //     'mobile'            => credential_encrypt($oldUser->mobile),
                    //     'address'           => credential_encrypt($oldUser->address),
                    //     'pincode'           => credential_encrypt($oldUser->pincode),
                    //     'gender'            => credential_encrypt($oldUser->gender == 'M' ? 'Male' : 'Female'),
                    //     'status'            => $oldUser->status == 'Active' ? 'Y' : 'N',
                    //     'usertype'          => 2,
                    //     'bank_branch'       => credential_encrypt($oldUser->bank_branch_name),
                    //     'account_no'        => credential_encrypt($oldUser->bank_account_no),
                    //     'ifsc_code'         => credential_encrypt($oldUser->ifsc_code),
                    //     'bank_name'         => credential_encrypt($oldUser->bank_name),
                    //     'account_holder_name'      => credential_encrypt($oldUser->name_of_bank_account),
                    //     'pan_no'            => credential_encrypt($oldUser->pan_no),
                    //     'adhar_no'         => credential_encrypt($oldUser->aadhar_no),
                    //     'employee_code'     => $oldUser->employee_code,
                    //     'pos_code'     => $oldUser->pos_code,
                    //     'old_user_id'       => $oldUser->agent_id,
                    //     'is_admin'          => $oldUser->level == 1 ? 'Y' : 'N',
                    //     'created_at'        => now(),
                    //     'updated_at'        => now(),
                    // ]);
                    
                    

                    DB::table($table)->where('mobile', $oldUser->mobile)->update(['creation_status' => 1]);
                    DB::table('users')->where('id', $newUserId)->update(['old_user_id' => $oldUser->$idColumn]);

                    $existingUserModel = DB::table('model_has_roles')->where('model_id', $newUserId)->where('role_id', $oldUser->mapping_role)->exists();
                    if(!$existingUserModel){
                        DB::table('model_has_roles')->insert([
                            'role_id'    => $oldUser->mapping_role,
                            'model_type' => 'App\Models\User',
                            'model_id'   => $newUserId
                        ]);    
                    }
                    Log::info("New user created with ID: $newUserId");

                    Log::info("Assigned roles and lob to role ID: {$oldUser->mapping_role}");

                    $lob_ids = [1, 2, 3, 4, 5, 6, 8];
                    foreach ($lob_ids as $lob_id) {
                        DB::table('user_lob_relation')->insert([
                            'user_id' => $newUserId,
                            'lob_id'  => $lob_id,
                        ]);
                    }
                }
            } elseif ($type === 'mapping') {
                // if ($existingUser) {
                if ($existingUser ) {

                    $sameUsertypeExits= DB::table('users')->where('id', $existingUser->id)->where('usertype', $userType)->first();
                    if ($sameUsertypeExits) {
                        $oldReportingUser = DB::table($table)->where($idColumn, $oldUser->$supervisorColumn)->first();
                        if ($oldReportingUser) { 
                            $newReportinhUser = DB::table('users')->where('old_user_id', $oldReportingUser->$idColumn)->first();
                            if ($newReportinhUser) {
                            DB::table('users')->where('id', $existingUser->id)->update(['reportingto' => $newReportinhUser->id]);
                            DB::table($table)->where('mobile', $oldUser->mobile)->update(['mapping_status' => 1]);
                            Log::info("Mapped reporting user for ID: {$existingUser->id}");
                            }
                        }
                    }else {
                        $sameUsertypeExits= DB::table('user_mappings')->where('user_id', $existingUser->id)->where('user_type', $userType)->first();
                        if ($sameUsertypeExits) {
                            $oldReportingUser = DB::table($table)->where($idColumn, $oldUser->$supervisorColumn)->first();
                        if ($oldReportingUser) { 
                            $newReportinhUser = DB::table('users')->where('old_user_id', $oldReportingUser->$idColumn)->first();
                            if ($newReportinhUser) {
                            DB::table('user_mappings')->where('user_id', $existingUser->id)->update(['reportingto' => $newReportinhUser->id]);
                            DB::table($table)->where('mobile', $oldUser->mobile)->update(['mapping_status' => 1]);
                            Log::info("Mapped reporting user for ID: {$existingUser->id}");
                            }
                        }else {
                            DB::table($table)->where('mobile', $oldUser->mobile)->update(['mapping_status' => 1]);

                        }
                        }
                        
                    }

                } else {
                    $failed[] = ['old_user_id' => $oldUser->$idColumn, 'error' => 'This is not an existing User'];
                }
            } elseif (in_array($type, ['motor_mapping', 'health_mapping'])) {
                if (!$existingUser) {
                    $failed[] = ['old_user_id' => $oldUser->$idColumn, 'error' => 'User not found'];
                    continue;
                }

                $apiUrl = $type === 'motor_mapping' ? $otherApi : $healthApi;
                $logLabel = $type === 'motor_mapping' ? 'MOTOR' : 'HEALTH';

                $requestData = [
                    'seller_type' => 'E',
                    'employee_id'    => $oldUser->$idColumn,
                    'new_data'    => ['employee_id' => $existingUser->id],
                ];

                $response = Http::withHeaders([
                    'Content-Type' => 'application/json',
                    'validation'   => $motorToken,
                ])->post($apiUrl, $requestData);

                // Log request and response
                Log::channel('single')->info("[$logLabel] Mapping Request", [
                    'api_url' => $apiUrl,
                    'request_payload' => $requestData,
                    'response_status' => $response->status(),
                    'response_body' => $response->body(),
                    'user_id' => $existingUser->id,
                    'old_user_id' => $oldUser->$idColumn,
                ]);

                if ($response->successful()) {
                    DB::table($table)->where('mobile', $oldUser->mobile)->update([
                        $type === 'motor_mapping' ? 'motor_mapping_status' : 'health_mapping_status' => 1
                    ]);
                } else {
                    $failed[] = ['old_user_id' => $oldUser->$idColumn, 'error' => $response->body()];
                }
            }

            $migratedCount++;
        }

        return response()->json([
            'status' => true,
            'migrated_count' => $migratedCount,
            'failed' => $failed,
        ]);
    // } catch (\Exception $e) {
    //     dd($e->getMessage(), $e->getFile(), $e->getLine());
    // }
    }


}
