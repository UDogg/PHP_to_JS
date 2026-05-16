<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Imports\UsersImport;
use Maatwebsite\Excel\Facades\Excel;
use App\Models\User;
use App\Models\PospIcMapping;
use PhpParser\Node\Stmt\Return_;
use Illuminate\Support\Facades\Schema;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Storage;
use App\Models\masterCompany;
use PhpOffice\PhpSpreadsheet\Spreadsheet;
use PhpOffice\PhpSpreadsheet\Writer\Xlsx;
use App\Models\userTypes;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Str;
use App\Models\SSO;
class PospIcMappingController extends Controller
{
    public function icMappingSample(Request $request){
        $filePath = 'Sample_posp_data.xlsx';
        
        if(!Storage::disk('public')->exists($filePath)){
            return response()->json([
                'status' => 404,
                'message' => 'File Not Found!',
            ], 404);
        }

        $fileUrl = Storage::disk('public')->url($filePath);
        return response()->json([
            'status' => 200,
            'message' => 'Sample Link',
            'file_url' => $fileUrl 
        ]);
    }



    public function pospIcMappingUpload(Request $request)
    {
        $userdetials = Auth::user();
        $uploadPermission = 'POS ic mapping.upload';
        if (!$userdetials->can($uploadPermission)) {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to perform this action.'
            ], 403);
        }
        $success = [];
        $error = [];
        $invalidRows = [];

        $request->validate([
            'excel_upload' => 'required|mimes:xlsx,xls,csv',
            'mapping_as_per' => 'required|in:username,pan_no,adhar_no',
            'insurance_company' => 'required|string',
        ]);

        if (!$request->hasFile('excel_upload')) {
            return response()->json(["status" => 400, "message" => "No file uploaded. Please select a valid Excel file and try again."]);
        }

        $excelData = self::import($request);
        if (empty($excelData)) {
            return response()->json(["status" => 400, "message" => "No Data Found in Excel"]);
        }

        $company = masterCompany::where('company_name', $request->insurance_company)->first();
        if (!$company) {
            return response()->json(["status" => 400, "message" => "Company name not found"]);
        }

        $headers = array_map('trim', $excelData[0]);
        $dataRows = array_slice($excelData, 1);

        $headers[] = 'Status';
        $fieldMapping = [
            'username' => 'username',
            'pan_no' => 'pan_no',
            'adhar_no' => 'adhar_no'
        ];

        $field = $fieldMapping[$request->mapping_as_per] ?? null;
        $fieldIndex = array_search(ucfirst($field), $headers);

        if ($fieldIndex === false) {
            return response()->json(["status" => 400, "message" => "Mapping field '{$field}' not found in Excel"]);
        }

        $posCodeIndex = array_search('POS_Code', $headers);
        if ($posCodeIndex === false) {
            return response()->json(["status" => 400, "message" => "POS_Code column not found in Excel"]);
        }

        $companyColumn = $company->company_shortname;
        if (!Schema::hasColumn('posp_ic_mappings', $companyColumn)) {

            Schema::table('posp_ic_mappings', function (Blueprint $table) use ($companyColumn) {
                $table->string($companyColumn)->nullable();
            });
        }

        $userFoundCount = 0;
        $userNotFoundCount = 0;

        foreach ($dataRows as &$data) {
            if (!isset($data[$fieldIndex]) || empty(trim($data[$fieldIndex]))) {
                $data[] = "Missing {$field}";
                $invalidRows[] = $data;
                continue;
            }
    
            $value = credential_encrypt(trim($data[$fieldIndex]));
            $user = User::where($field, $value)
                ->where(function ($query) {
                    $query->where('usertype', 2)
                        ->orWhereIn('usertype', function ($subQuery) {
                            $subQuery->select('id')
                                    ->from('usertypes')
                                    ->whereIn('Identifier', ['P','SP'])
                                    ->where('is_active', 'Y');
                        });
                })
                ->first();

            $decryptedValue = credential_decrypt($value);

            if ($user) {
                $success[] = "{$field} '{$decryptedValue}' found.";
                $data[] = "User Found";
                $userFoundCount++;

                PospIcMapping::updateOrCreate(
                    ['user_id' => $user->id], 
                    [
                        'user_id' => $user->id,
                        $companyColumn => $data[$posCodeIndex] ?? null 
                    ]
                );
            } else {
                $error[] = "{$field} '{$decryptedValue}' not found.";
                $data[] = "User Not Found";
                $userNotFoundCount++;
                $invalidRows[] = $data;
            }

        }

        if (!empty($invalidRows)) {
            $fileUrl = $this->generateErrorExcel($headers, $invalidRows);
            return response()->json([
                "status" => 400,
                "message" => "Mapping failed. Download updated Excel file for details.",
                "errors" => $error,
                "file_url" => $fileUrl,
                "user_found_count" => $userFoundCount,
                "user_not_found_count" => $userNotFoundCount
            ]);
        }
        if ($userFoundCount == 0) {
            return response()->json([
                "status" => 400,
                "message" => "No users found for mapping.",
                "user_found_count" => $userFoundCount,
                "user_not_found_count" => $userNotFoundCount
            ]);
        }

        return response()->json([
            "status" => 200,
            "message" => "All users found and mapped successfully.",
            "user_found_count" => $userFoundCount
        ]);
    }


    private function generateErrorExcel($headers, $dataRows)
    {
        $filePath = 'IC_Mapping/Error_posp_data.xlsx';

        $spreadsheet = new Spreadsheet();
        $sheet = $spreadsheet->getActiveSheet();

        // Write headers and data to the sheet
        $sheet->fromArray([$headers], null, 'A1'); 
        $sheet->fromArray($dataRows, null, 'A2'); 

        // Save the file to storage
        Storage::disk('public')->put($filePath, '');
        $writer = new Xlsx($spreadsheet);
        $writer->save(storage_path("app/public/{$filePath}"));

        return Storage::disk('public')->url($filePath);
    }

    public function getAllPospIcMappings(){

        $mappings = PospIcMapping::with(['user:id,name,middle_name,last_name'])->get()
        ->map(function ($mapping) {
    
        $data = [
            'name' => credential_decrypt(optional($mapping->user)->name).' '.
                      credential_decrypt(optional($mapping->user)->middle_name).' '.
                      credential_decrypt(optional($mapping->user)->last_name),
        ] + collect($mapping->toArray())
            ->except(['id', 'user_id', 'user', 'created_at', 'updated_at'])
            ->toArray();
    
        return collect($data)
            ->mapWithKeys(fn ($value, $key) => [ucfirst($key) => $value])
            ->toArray();
        });
    
        return response()->json(["status" => 200, "data" => $mappings->isNotEmpty() ? $mappings : []]);
    }


    public function getPospData(Request $request)
    {
        $success = [];
        $error = [];
    
        if (empty($request->excel_upload)) {
            return [
                "status" => 400,
                "message" => "Issue with excel upload"
            ];
        }
    
        $excelData = self::import($request);
    
        if (empty($excelData)) {
            return [
                "status" => 400,
                "message" => "No Data Found in Excel"
            ];
        }
    
        $mapping = $request->mapping_as_per ?? '';
        $columnName = $request->insurance_company ?? '';
        $relationColumn = $columnName . "_relation";
    
        foreach ($excelData as $key => $value) {
            $username = credential_encrypt($value['Username']);
            $userData = User::select('id')->where($mapping, $username)->first();

            if ($value['POS_Code'] == 'POS Code' && $value['Username'] == 'Username') {
            continue;
            }

            if (!empty($userData)) {
                if (!Schema::hasColumn('posp_ic_mappings', $relationColumn)) {
                    Schema::table('posp_ic_mappings', function (Blueprint $table) use ($relationColumn) {
                        $table->string($relationColumn)->nullable();
                    });
                    Log::info("Column '$relationColumn' added to 'posp_ic_mappings' table.");
                } else {
                    Log::info("Column '$relationColumn' already exists.");
                }
                $newRow = PospIcMapping::updateOrCreate(
                    ['posp_id' => $userData->id],
                    [$relationColumn => $value['POS_Code']]
                );
                if ($newRow) {
                    $success[] = [
                        "status" => 200,
                        "message" => "Success",
                        "username" => credential_decrypt($username),
                        "posp_id" => $value['POS_Code'],
                    ];
                } else {
                    $error[] = [
                        "status" => 400,
                        "message" => "Issue in creating a new row",
                        "username" => credential_decrypt($username),
                        "posp_id" => $value['POS_Code'],
                    ];
                }
            } else {
                $error[] = [
                    "status" => 400,
                    "message" => "User Not Found",
                    "username" => credential_decrypt($username),
                    "posp_id" => $value['POS_Code'],
                ];
            }
        }
        return [
            "status" => 200,
            "return Message" => [
                "success" => $success,
                "error" => $error
            ]
        ];
    }
    


    public function import(Request $request)
    {
        $request->validate([
            'excel_upload' => 'required|mimes:xlsx,xls,csv',
        ]);

        $import = new UsersImport;
        $data = Excel::toArray($import, $request->file('excel_upload'));

        return $data[0] ?? []; 
    
    }


    public function getPospList() { 
        $results = PospIcMapping::select('posp_ic_mappings.*', 'users.name', 'users.mobile', 'users.adhar_no', 'users.pan_no')
        ->join('users', 'posp_ic_mappings.posp_id', '=', 'users.id')
        ->get();
    
        $data = [];
        foreach ($results as $key => $value) {
            $value->name = credential_decrypt($value->name);
            $value->mobile = credential_decrypt($value->mobile);
            $value->adhar_no = credential_decrypt($value->adhar_no);
            $value->pan_no = credential_decrypt($value->pan_no);
            $data [] = $value;
        }
        if (!empty($data)) { 
           return ([
               'status' => "200",
               'data' => $data
           ]); 
        } else { 
            return ([
                'status' => "500",
                'message' => "Data not found",
            ]);
        }
    }

    public function createToken(Request $request)
    {
        $request->validate([
            'username' => 'required|string',
            'password' => 'required'
        ]);

        $username = config('auth.username');
        $password = config('auth.password');
        if ($request->username == $username && $request->password == $password) {

            $uuidToken = Str::uuid()->toString();
            $expiryMinutes = config('auth.token_expiry', 30);
            //converting timezone
            $expiryTime = date("d/m/Y h:i a", strtotime("+$expiryMinutes minutes", time() + 19800));

            SSO::create([
                'sso_api_token' => $uuidToken,
                'status' => 'Y'
            ]);

            return response()->json([
                'message' => 'Token Generated',
                'token' => $uuidToken,
                'expires_in' => $expiryTime
            ], 200);
        } else {
            return response()->json(['message' => 'Invalid credentials'], 401);
        }
    }
    public function getDetailpospData(Request $request)
    {
        $token = $request->bearerToken();
    
        // Fetch users and their mappings
        $pospData = PospIcMapping::rightJoin('users', 'posp_ic_mappings.user_id', '=', 'users.id')
            ->select('users.id as agent_id', 'users.*', 'posp_ic_mappings.*')
            ->where('users.usertype', '2')
            ->where('users.is_admin', 'N')
            ->get()
            ->makeHidden(['created_at', 'updated_at', 'ic', 'id', 'password']);
    
        $rowCount = $pospData->count();
    
        $decryptedData = $pospData->map(function ($record) {
            $decrypted = [];
            foreach ($record->toArray() as $key => $value) {
                $decrypted[$key] = credential_decrypt($value);
            }
    
            // Decrypt name fields
            $first_name = isset($record->name) ? credential_decrypt($record->name) : '';
            $middle_name = isset($record->middle_name) ? credential_decrypt($record->middle_name) : '';
            $last_name = isset($record->last_name) ? credential_decrypt($record->last_name) : '';
    
            // Construct agent name
            $agent_name = trim(preg_replace('/\s+/', ' ', "$first_name $middle_name $last_name"));
            $decrypted['agent_name'] = $agent_name ?: '';
            $decrypted['unique_number'] = $record->pos_code;
            $decrypted['first_name'] = $first_name;
            $decrypted['user_name'] = credential_decrypt($record->user_name);
            $decrypted['father_name'] = '';
            $decrypted['phone_no'] = credential_decrypt($record->mobile_no);
            $dob = $record->dob ? credential_decrypt($record->dob) : '';
            $decrypted['date_of_birth'] = $dob ? date('Y-m-d', strtotime($dob)) : '';

            // $decrypted['date_of_birth'] = $record->dob ? credential_decrypt($record->dob) : '';
            $decrypted['marital_status'] = '';
            $decrypted['aadhar_no'] = $record->adhar_no ? credential_decrypt($record->adhar_no) : '';
    
            // Decrypt pincode
            $pincode = $record->pincode ? credential_decrypt($record->pincode) : null;
    
            // Fetch city and state based on pincode
            if ($pincode) {
                $location = DB::table('pincode_masters as pm')
                    ->leftJoin('city_masters as cm', 'cm.city_id', '=', 'pm.city_id')
                    ->leftJoin('state_masters as sm', 'sm.state_id', '=', 'pm.state_id')
                    ->select('cm.city_name', 'sm.state_name')
                    ->where('pm.pincode', $pincode)
                    ->first();
            
                $decrypted['city'] = $location->city_name ?? '';
                $decrypted['state'] = $location->state_name ?? '';
            } else {
                $decrypted['city'] = '';
                $decrypted['state'] = '';
            }
    
            $decrypted['parent'] = '';
            $decrypted['usertype'] = 'P';
            $decrypted['status'] = 'Active';
            $decrypted['level'] = 0;
            $decrypted['supervisor_name'] = '';
            $decrypted['supervisor_emp_code'] = '';
            $decrypted['supervisor_mobile'] = '';
            $decrypted['rm_branch'] = '';
            $decrypted['allowed_sections'] = '';
            $decrypted['comm_percent'] = '';
            $licence_start_date = $record->license_start_date ? credential_decrypt($record->license_start_date) : '';
            $licence_end_date = $record->license_end_date ? credential_decrypt($record->license_end_date) : '';

            $decrypted['licence_start_date'] = $licence_start_date ? date('Y-m-d', strtotime($licence_start_date)) : '';
            $decrypted['licence_end_date'] = $licence_end_date ? date('Y-m-d', strtotime($licence_end_date)) : '';

            // $decrypted['licence_start_date'] = credential_decrypt($record->license_start_date);
            // $decrypted['licence_end_date'] = credential_decrypt($record->license_end_date);
    
            return $decrypted;
        });
    
        return $rowCount === 0
            ? response()->json(['message' => 'No data found'], 404)
            : response()->json([
                'success' => true,
                'message' => "Data found: " . $rowCount,
                'data' => $decryptedData,
            ], 200);
    }

}