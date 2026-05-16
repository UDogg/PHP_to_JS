<?php

namespace App\Http\Controllers;

use App\Exports\CorporateUserWhitelistExport;
use App\Models\CorporateUserWhitelisting;
use Exception;
use App\Models\MongoModel;
use Illuminate\Support\Str;
use Illuminate\Http\Request;
use App\Exports\AllDataExport;
use App\Jobs\ExportLargeExcel;
use Illuminate\Support\Carbon;
use App\Models\ExcelDownloadLog;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\Auth;
use Maatwebsite\Excel\Facades\Excel;
use App\Models\CorporateDomainMapping;
use Illuminate\Support\Facades\Storage;
use App\Imports\EmailWhitelistingImport;
use App\Models\corporatesOnBoardingMaster;
use Illuminate\Validation\ValidationException;
use App\Http\Controllers\PospIcMappingController;
use App\Models\Customer;
use App\Models\WhiteListingCorporatesOnBoardingModel;
use Illuminate\Support\Facades\Validator;

class CorporatesController extends Controller
{
    protected $Auth;
    public function __construct()
    {
        $this->Auth = Auth::user();
    }

    public function newGetData(Request $request){

        $query = CorporatesOnBoardingMaster::query();
        $page = $request->page;
        $perPage = $request->input('perPageRecords', 10);

        if ($request->has('search') && !empty($request->search)) {
            $searchTerm = $request->search;

            $query->where(function ($q) use ($searchTerm) {
                $q->where('company_name', 'LIKE', "%{$searchTerm}%")
                    ->orWhere('work_email', 'LIKE', "%{$searchTerm}%")
                    ->orWhere('first_name', 'LIKE', "%{$searchTerm}%")
                    ->orWhere('mobile_no', 'LIKE', "%{$searchTerm}%");
            });
        }
    
        if ($request->has('paginate') && $request->paginate == 'true') {
  
            $paginatedData = $query->paginate($perPage);
            
            $result = $paginatedData->map(function ($data,$index) use($page,$perPage)  {
                $serial = ($page - 1) * $perPage + ($index + 1);
                return $this->transformCorporatesOnBoardingMasterData($data,$serial);
            });

            $prevPage = $paginatedData->currentPage() - 1;
            $nextPage = $paginatedData->currentPage() + 1;
    
            return response()->json([
                'status' => 200,
                'data' => $result,
                'pagination' => [
                    'per_page' => $paginatedData->perPage(),
                    'page' => $paginatedData->currentPage(),
                    'prev_page' => $prevPage > 0 ? $prevPage : null, // Return null if there is no previous page
                    'next_page' => $nextPage <= $paginatedData->lastPage() ? $nextPage : null, // Return null if there is no next page
                    'total' => $paginatedData->total(),
                    'last_page' => $paginatedData->lastPage(),
                ]
                
            ]);
    
        } else {
            $datas = $query->get();
    
            $result = $datas->map(function ($data,$index) use($page,$perPage) {
                $serial = ($page - 1) * $perPage + ($index + 1);
                return $this->transformCorporatesOnBoardingMasterData($data,$serial);
            });
    
            return response()->json([
                'status' => "true",
                'data' => $result,
            ]);
        }
        //export
    }

    private function transformCorporatesOnBoardingMasterData($data,$index)
    {
        
        return [
            "Sr No" => $index,
            "master_id" => $data->id,
            "first_name" => $data->first_name,
            "last_name" => $data->last_name, 
            "company_name" => $data->company_name,
            "designation" => $data->designation,
            "work_email" => $data->work_email,
            "corporates_mobile_no" => $data->mobile_no,
            "no_of_employees" => $data->no_of_employees,
            "is_verified" => $data->is_verified ?? null,
            "is_verified_required_to" =>$data->is_verified_required_to ?? null,
            "other_email" => $data->other_email,  
            "company_domain" => $data->company_domain,
            "corporates_status" => $data->status,
            "document" => $data->document ?? null,
            "selected_domain" => $data->selected_domain ?? null,           
            "created_at" => $data->created_at,
            "updated_at" => $data->updated_at,
        ];
    }
    public function getData(Request $request)
    {
        $request->validate([
            'page' => 'integer',
            'perPageRecords' => 'integer',
            'pagination' => 'boolean',
            'export' => 'boolean',
            'search' => 'nullable|string',
        ]);
    
        $pagination = $request->input('pagination', true);
        $page = $request->input('page', 1);
        $perPageRecords = $request->input('perPageRecords', 10);
        $search = $request->input('search', '');
    
        $query = CorporatesOnBoardingMaster::select([
            'corporates_on_boarding_master.id as master_id',
            'corporates_on_boarding_master.mobile_no as corporates_mobile_no',
            'corporates_on_boarding_master.status as corporates_status',
            'corporates_on_boarding_master.*',
            'b.corporates_on_boarding_id as whitelisted_onboarding_id',
            'b.*',
            'd.domain_name as selected_domain',
            DB::raw("IFNULL(b.status, 'Inactive') as whitelist_status")
        ])
        ->leftJoin(DB::raw('(
            SELECT corporates_on_boarding_id, MIN(id) as min_id
            FROM white_listing_corporates_on_boarding_master
            GROUP BY corporates_on_boarding_id
        ) as b_min'), 'corporates_on_boarding_master.id', '=', 'b_min.corporates_on_boarding_id')
        ->leftJoin('white_listing_corporates_on_boarding_master as b', 'b_min.min_id', '=', 'b.id')
        ->leftJoin(DB::raw('(
            SELECT corporate_id, MIN(id) as min_domain_id
            FROM corporate_domain_mapping
            WHERE is_verified = "Y"
            GROUP BY corporate_id
        ) as d_min'), 'corporates_on_boarding_master.id', '=', 'd_min.corporate_id')
        ->leftJoin('corporate_domain_mapping as d', 'd_min.min_domain_id', '=', 'd.id');
    
        if (!empty($search)) {
            $query->where(function ($query) use ($search) {
                $query->where('first_name', 'LIKE', "%{$search}%")
                    ->orWhere('last_name', 'LIKE', "%{$search}%")
                    ->orWhere('company_name', 'LIKE', "%{$search}%")
                    ->orWhere('company_domain', 'LIKE', "%{$search}%")
                    ->orWhere('corporates_on_boarding_master.mobile_no', 'LIKE', "%{$search}%")
                    ->orWhere('work_email', 'LIKE', "%{$search}%");
            });
        }

        if ($pagination) {
            $corporateOnBoarding_data = $query->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $corporateOnBoarding_data->lastPage();
            $totalCount = $corporateOnBoarding_data->total();
            $prevPage = $corporateOnBoarding_data->previousPageUrl() ? $page - 1 : null;
            $nextPage = $corporateOnBoarding_data->nextPageUrl() ? $page + 1 : null;
            $corporateOnBoarding_data = $corporateOnBoarding_data->toArray()['data'];
            
            if ($request->input('export', false)) {
                $dataCount = $query->count();
                $maxAllowedCount = config('excel.data.limit.download');
                $headings = [
                    'S.no', 'First Name', 'Last Name', 'Organization Name', 'Designation', 'Email', 'Mobile No.',
                    'No. of Employees', 'Domain', 'Referral Email Id', 'Verification Required', 'Corporate Status'
                ];
    
                if ($dataCount > $maxAllowedCount) {
                    $log = ExcelDownloadLog::insert([
                        'user_id' => Auth::id(),  
                        'request' => json_encode($request->all()),
                        'status' => '0',
                        'created_at' => Carbon::now(),
                        'source' => 'CORPORATE_ON_BOARDING Data Export'
                    ]);
                    $random = rand(1, 10000000);
                    $filename = 'Data/CORPORATE_ON_BOARDING' . $random . '.xlsx';
                    ExportLargeExcel::dispatch($corporateOnBoarding_data, $headings, $request->all(), Auth::id(), 'CORPORATE_ON_BOARDING', $filename)
                        ->onQueue('LargeExcelExports');
                    
                    return response()->json([
                        'status' => 200,
                        'message' => 'Data is too large to download. Added to Queue. You will get this file later in job list.'
                    ]);
                } else {
                    $corporateOnBoarding_data_array = $corporateOnBoarding_data->map(function($item, $index) {
                        return [
                            'S.no' => $index + 1,
                            'First Name' => $item->first_name,
                            'Last Name' => $item->last_name,
                            'Organization Name' => $item->company_name,
                            'Designation' => $item->designation,
                            'Email' => $item->work_email,
                            'Mobile No.' => $item->mobile_no,
                            'No. of Employees' => $item->employees_count,
                            'Domain' => $item->company_domain,
                            'Referral Email Id' => $item->referral_email_id,
                            'Verification Required' => $item->verification_required ? 'Yes' : 'No',
                            'Corporate Status' => $item->corporates_status
                        ];
                    })->toArray();  
    
                    $export = new AllDataExport($corporateOnBoarding_data_array, $headings, 'CORPORATE_ON_BOARDING');
                    $random = Str::random(10);
                    $filePath = 'Data/CORPORATE_ON_BOARDING' . $random . '.xlsx';
                    Excel::store($export, $filePath, 'public');
                    $downloadLink = Storage::disk('public')->url($filePath);
                    ExcelDataExportLog(Auth::id(), $filePath, 'CORPORATE_ON_BOARDING', 'completed', $request->all());
    
                    return response()->json([
                        'status' => 200,
                        'message' => 'Excel file generated successfully',
                        'link' => $downloadLink,
                    ]);
                }
            }
    
            return response()->json([
                'status' => 200,
                'data' => $corporateOnBoarding_data,
                'pagination' => [
                    'pagination_type' => 'integrated',
                    'per_page' => $perPageRecords,
                    'current_page' => $page,
                    'prev_page_page' => $prevPage,
                    'next_page_page' => $nextPage,
                    'total' => $totalCount,
                    'last_page' => $lastPage,
                ]
            ]);
        } else {
            $corporateOnBoarding_data = $query->get();
            $totalCount = $corporateOnBoarding_data->count();
    
            return response()->json([
                'status' => 200,
                'data' => $corporateOnBoarding_data,
                'total' => $totalCount,
            ]);
        }
    }
    public function updateCorporatesData(Request $request)
    {
        if (!$request->has(['firstname', 'company_name', 'work_email_id', 'mobile_no'])) {
            return response()->json([
                "status" => 500,
                "message" => "Required fields are missing"
            ]);
        }

        $firstName = $request->firstname;
        $lastName = $request->lastname;
        $companyName = $request->company_name;
        $designation = $request->designation;
        $workEmail = $request->work_email_id;
        $mobileNo = $request->mobile_no;
        $noOfEmployees = $request->no_of_employees ?? 0;
        $isVerified = $request->is_verified;
        $otherEmail = $request->other_email_id;
        $isVerifiedRequiredTo = $request->is_verification_required_to;
        $selectedDomain = $request->selected_domain;
        $companyId = $request->id;

        $companyDomainInput = $request->company_domain;
        $companyDomainArray = is_array($companyDomainInput) ? $companyDomainInput : explode(',', $companyDomainInput);

        // $existingDomains = corporatesOnBoardingMaster::whereIn('company_domain', $companyDomainArray)
        //     ->where('id', '!=', $companyId)
        //     ->pluck('company_domain')
        //     ->toArray();

        $existingDomains = corporatesOnBoardingMaster::whereIn('company_domain', $companyDomainArray);
        if (!empty($companyId)) {
            $existingDomains->where('id', '!=', $companyId);
        }
        $existingDomains = $existingDomains->pluck('company_domain')->toArray();

        if (!empty($existingDomains)) {
            return response()->json([
                "status" => 500,
                "message" => "The following domains already exist: " . implode(', ', $existingDomains) . ". Please choose different domains."
            ]);
        }

        $documentUrl = '';
        if ($request->hasFile('document')) {
            $document = $request->file('document');
            $documentPath = $document->store('documents', 'public');
            $documentUrl = asset('storage/' . $documentPath);
        }


        $emailCheckQuery = corporatesOnBoardingMaster::where('work_email', $workEmail);
        if (!empty($companyId)) {
            $emailCheckQuery->where('id', '!=', $companyId);
        }
        if ($emailCheckQuery->exists()) {
            return response()->json([
                "status" => 500,
                "message" => "Email already exists. Please try with another email."
            ]);
        }

        $mobileCheckQuery = corporatesOnBoardingMaster::where('mobile_no', $mobileNo);
        if (!empty($companyId)) {
            $mobileCheckQuery->where('id', '!=', $companyId);
        }
        if ($mobileCheckQuery->exists()) {
            return response()->json([
                "status" => 500,
                "message" => "Mobile No already exists. Please try with another Mobile No."
            ]);
        }

      
        $existingCompany = corporatesOnBoardingMaster::where('company_name', $companyName);
        if (!empty($companyId)) {
            $existingCompany->where('id', '!=', $companyId);
        }
        if ($existingCompany->exists()) {
            return response()->json([
                "status" => 500,
                "message" => "company already exists."
            ]);
        }
                
          
        $userDetails = [];
        $userDetails = [
                    'first_name' => $firstName,
                    'last_name' => $lastName,
                    'company_name' => $companyName,
                    'designation' => $designation,
                    'work_email' => $workEmail,
                    'mobile_no' => $mobileNo,
                    'no_of_employees' => $noOfEmployees,
                    'is_verified' => $isVerified,
                    'other_email' => $otherEmail,
                    'is_verified_required_to' => $isVerifiedRequiredTo,
                    'document' => $documentUrl ?: null,
                    'company_domain' => implode(',', $companyDomainArray),
                    'selected_domain' => $selectedDomain ?? null
        ];
        if (!empty($companyId)) {
            $company = corporatesOnBoardingMaster::updateOrCreate(
                ['id' => $companyId],
                $userDetails
                
            );
        } else {
            $company = corporatesOnBoardingMaster::create(
                $userDetails
            );
        }

        

        if ($company && !empty($companyDomainArray)) {
            foreach ($companyDomainArray as $domain) {
                CorporateDomainMapping::updateOrCreate(
                    [
                        'domain_name' => trim($domain),
                        'corporate_id' => $company->id
                    ],
                    [
                        'status' => $request->status,
                        'is_verified' => $isVerified
                    ]
                );
            }
        }

        if ($company) {
            return response()->json([
                "corporates_id" => $company->id,
                "status" => 200,
                "message" => "Data successfully " . ($company->wasRecentlyCreated ? 'inserted' : 'updated')
            ]);
        } else {
            return response()->json([
                "status" => 500,
                "message" => "Error in processing data"
            ]);
        }
    }

    public function updateCorporatesDataStatus(Request $request)
    {
        $request->validate([
            'master_id' => 'required|integer',
        ]);
        $id = $request->master_id;
        $status = $request->status;

        $company = corporatesOnBoardingMaster::where('id', $id)->update(['status' => $status]);

        if ($company) {
            return response()->json(['success' => true, 'message' => 'Status updated successfully']);
        } else {
            return response()->json(['success' => false, 'message' => 'Failed to update status']);
        }
    }

    public function updateCorporatesDataVerfication(Request $request)
    {
        $request->validate([
            'master_id' => 'required|integer',
            'is_verified_required_to' => 'required',
        ]);
    
        $id = $request->master_id;
        $is_verified_required_to = $request->is_verified_required_to;
        $companyDomains = explode(',', $request->company_domain); 
        $is_verified = $request->is_verified;
    
        $allUpdatesSuccessful = true; 

        
        if($is_verified_required_to == 'Domain_Level'){
            CorporateDomainMapping::where('corporate_id', $id)->delete();
            foreach ($companyDomains as $domain) {
                $domainUpdate = CorporateDomainMapping::create([
                    'domain_name' => $domain,
                    'corporate_id' => $id,
                    'is_verified' => $is_verified
                ]);
        
                if (!$domainUpdate) {
                    $allUpdatesSuccessful = false;
                }
            }
            $companyUpdate = corporatesOnBoardingMaster::where('id', $id)
            ->update([
                'is_verified_required_to' => $is_verified_required_to
            ]);
        }else{
            $companyUpdate = corporatesOnBoardingMaster::where('id', $id)
            ->update([
                'is_verified_required_to' => $is_verified_required_to,
                'is_verified' => $is_verified
            ]);
        }
    
        if ($allUpdatesSuccessful && $companyUpdate) {
            return response()->json(['success' => true, 'message' => 'Status updated successfully']);
        } else {
            return response()->json(['success' => false, 'message' => 'Failed to update status']);
        }
    }

    public function whiteListingCorporatesDomainList(Request $request)
    {
        $request->validate([
            'master_id' => 'required|integer',
        ]);
        $id = $request->master_id;

        $DomainList = CorporateDomainMapping::where('corporate_id', $id)
                    ->get();
        if (!empty($DomainList)) {
            $data  = $DomainList->toArray();
            return ([
                "status" => 200,
                "data" => $data
            ]);
        } else {
            return ([
                "status" => 500,
                "message" => "No Data Found"
            ]);
        }
        return $resposnse;

    }

    public function whiteListingCorporatesData(Request $request)
    {
        $response = [];
        $request->validate([
            'master_id' => 'required|integer',
        ]);

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

        $dataUpdated = false;

        foreach ($excelData as $key => $value) {
            if ($key === 0 && isset($value['Email_id'], $value['Mobile_No'], $value['Status']) &&
                $value['Email_id'] == 'Email_id' && 
                $value['Mobile_No'] == 'Mobile No.' && 
                $value['Status'] == 'Status') {
                continue;
            }

            if (!empty($value['Email_id']) && !empty($value['Mobile_No'])) {
                try {
                    // WhiteListingCorporatesOnBoardingModel::updateOrCreate(
                    CorporateUserWhitelisting::updateOrCreate(
                        [
                            'corporate_id' => $request->master_id,
                            'email' => credential_encrypt($value['Email_id']),
                            'mobile' => $value['Mobile_No'],
                        ],
                        [
                            'status' => $value['Status'] == 'Active' ? 1 : 0,
                        ]
                    );

                    $dataUpdated = true;
                } catch (Exception $e) {
                    $response[] = [
                        "corporates_on_boarding_id" => $request->master_id,
                        "status" => 500,
                        "message" => "Failed to update data: " . $e->getMessage()
                    ];
                }
            }
        }

        if ($dataUpdated) {
            return [
                "status" => 200,
                "message" => "Data Updated Successfully"
            ];
        } else {
            return [
                "status" => 500,
                "message" => "No Data Found"
            ];
        }
    }

    public function deleteWhiteListingCorporatesData(Request $request) {

        if (empty($request->email)) {
            return response()->json([
                "status" => 404,
                "message" => "No Email ID provided"
            ]);
        }

        $email = credential_encrypt($request->email);
        $status = $request->status;

        $whitelistUser = CorporateUserWhitelisting::where('email',$email)->where('status',0)->delete();

        $customerUser = Customer::where('email', $email)->where('status','N')->delete();

        if ($customerUser == 0 || $whitelistUser == 0) {
            return response()->json([
                "status" => 500,
                "message" => "Inactive the Customer first"
            ]);
        }

        return response()->json([
            "status" => 200,
            "message" => "Customer delete successfully"
        ]);

        
    }

    public function whiteListingCorporatesDataView(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'master_id' => 'required', 
        ]);

        if ($validator->fails()) {
            return response()->json([
                'success' => false,
                'message' => 'Validation error',
                'errors' => $validator->errors()
            ], 422); 
        }

        $page = $request->input('page', 1);
        $perPageRecords = $request->input('perPageRecords', 10);
        $search = $request->input('search', '');

        $query = CorporateUserWhitelisting::query();

        $corporateDomainId = $request->master_id;
        
        $query->where('corporate_id', $corporateDomainId);

        if ($request->has('search') && !empty($request->search)) {
            $search = credential_encrypt($request->search);
            if (!empty($search)) {
                $query->where(function ($q) use ($search) {
                    $q->where('mobile', 'LIKE', "%{$search}%")
                        ->orWhere('email', 'LIKE', "%{$search}%");
                });
            }
        }

        $query->select(['email','mobile','status']);
  
        $data = $query->paginate($perPageRecords);

        $formatted = $data->map(function ($item) {
            return [
                'email'   => credential_decrypt($item->email) ?? 'N/A',
                'mobile'  => $item->mobile ?? 'N/A',
                'status'  => $item->status == 1 ? 'Active' : 'Inactive',
            ];
        });

        if ($request->has('export') && $request->export == true) {

            $fileName = 'whitelist_users_' . time() . '.xlsx';
            $filePath = 'exports/' . $fileName;

            Excel::store(new CorporateUserWhitelistExport($formatted), $filePath, 'public');

            $downloadUrl = Storage::url($filePath);

            return response()->json([
                'message' => 'Excel file generated successfully.',
                'download_url' => asset($downloadUrl)
            ]);
        }

        if ($data->isNotEmpty()) {
            return response()->json([
                "status" => 200,
                "data" => $formatted,
                "pagination" => [
                    'pagination_type' => 'integrated',
                    'per_page' => $perPageRecords,
                    'current_page' => $data->currentPage(),
                    'prev_page' => $data->previousPageUrl() ? $page - 1 : null,
                    'next_page' => $data->nextPageUrl() ? $page + 1 : null,
                    'total' => $data->total(),
                    'last_page' => $data->lastPage(),
                ]
            ]);
        } else {
            return response()->json([
                "status" => 404,
                "message" => "No Data Found"
            ]);
        }
    }

    public function updateWhiteListingUserStatus(Request $request)
    {
        $request->validate([
            'email' => 'required|email',
            'status' => 'required|in:Active,Inactive',
        ]);

        $email = credential_encrypt($request->email);
        $status = $request->status;

        $whitelistUser = CorporateUserWhitelisting::where('email',$email)->first();

        if ($whitelistUser) {
            $whitelistUser->update([
                'status' => ($status == 'Active') ? 1 : 0
            ]);
        }

        $customerUser = Customer::where('email', $email)->first();

        if ($customerUser) {
            $customerUser->update([
                'status' => ($status == 'Active') ? 'Y' : 'N'
            ]);
        }

        return response()->json([
            "status" => 200,
            "message" => "Status Updated Successfully"
        ]);
    }

    public function import(Request $request)
    {
        $request->validate([
            'excel_upload' => 'required|mimes:xlsx,xls,csv',
        ]);

        $import = new EmailWhitelistingImport;
        Excel::import($import, $request->file('excel_upload'));

        $data = $import->getData();
        return ($data);
    }

    public function whiteListingCorporatesSampleExcel () {
        $filePath = 'samples/sample_corporates_onboarding.xlsx';
        $sourceFilePath = storage_path('app/public/samples/sample_corporates_onboarding.xlsx');

        if (file_exists($sourceFilePath)) {
            if (!Storage::disk('public')->exists($filePath)) {
                Storage::disk('public')->put($filePath, file_get_contents($sourceFilePath));
            }
            $fileUrl = asset('storage/' . $filePath);
            return response()->json(['file_url' => $fileUrl]);
        } else {
            return response()->json(['error' => 'Sample file not found.'], 404);
        }
    }

    public function editCorporatesData(Request $request)
    {
    
            if (empty($request->id)) {
                return response()->json([
                    "status" => 400,
                    "message" => "Invalid Request: ID is required"
                ], 400);
            }
 
                 $company_domain = $request->input('company_domain');
                 $company_domain = explode(',', $company_domain);
                 $is_verified = $request->input('is_verified');
                $updateData = [
                    'first_name' => $request->input('firstname'),
                    'last_name' => $request->input('lastname'),
                    'company_name' => $request->input('company_name'),
                    'designation' => $request->input('designation'),
                    'work_email' => $request->input('work_email_id'),
                    'other_email' => $request->input('other_email_id'),
                    'mobile_no' => $request->input('mobile_no'),
                    'no_of_employees' => $request->input('no_of_employees'),
                    'is_verified_required_to' => $request->input('is_verification_required_to'),
                    'is_verified' => $request->input('is_verified'),
                    'company_domain' => $request->input('company_domain'),
                    'selected_domain' => $request->input('selected_domain')
                ];

                // if the document url is provided then we will add it
    
                    if ($request->file('document')) {
                        $document = $request->file('document');
                        $documentPath = $document->store('documents', 'public');
                        $documentUrl = asset('storage/' . $documentPath);
                        $updateData['document'] = $documentUrl;
                    }
                    
                $response = corporatesOnBoardingMaster::where('id', $request->id)->update($updateData);

                if($request->input('is_verification_required_to') == 'Domain Level' || $request->input('is_verification_required_to') == 'Corporate Level' ){ 
                    CorporateDomainMapping::where('corporate_id', $request->id)->delete();
                    foreach ($company_domain as $domain) {
                        $domainUpdate = CorporateDomainMapping::create([
                            'domain_name' => $domain,
                            'corporate_id' => $request->id,
                            'is_verified' => $is_verified
                    ]);
                  }
                }

            if (!$response) {
                return response()->json([
                    "status" => 404,
                    "message" => "No Corporate Data Found"
                ], 404);
            }

        if ($request->has('status')) {
            $whitelistingUpdate = WhiteListingCorporatesOnBoardingModel::where('corporates_on_boarding_id', $request->id)
                ->update([
                    'status' => $request->status
                ]);

            if (!$whitelistingUpdate) {
                return response()->json([
                    "status" => 404,
                    "message" => "No WhiteListing Data Found"
                ], 404);
            }
        }

        return response()->json([
            "status" => 200,
            "message" => "Data Updated Successfully"
        ], 200);
    }
    

    public function domainValidation(request $request)
    {
        if (!empty($request)) {

            $email = $request->email;
            if (empty($email)) {
                return response()->json([
                    "status" => false,
                    "message" => "No Data Found"
                ]);
            }
            // $domain = explode('@', $email)[1];
            $data = corporatesOnBoardingMaster::where('work_email', 'LIKE', "%$email%")->first();
            if (!empty($data)) {
                return ([
                    "status" => true,
                    "data" => "Data Exist"
                ]);
            } else {
                return ([
                    "status" => false,
                    "message" => "No Data Found"
                ]);
            }
        } else {
            return ([
                "status" => false,
                "message" => "No Data Found"
            ]);
        }
    }

    public function deleteCorporatesData(Request $request) {
        if (empty($request->id)) {
            return response()->json([
                "status" => 404,
                "message" => "No ID provided"
            ]);
        }

        $trsactionStage = StageToSubStage("Issued");
        // Check if MongoModel has any records for the provided user_id
        $mongoRecords = MongoModel::where('user_id', $request->id)->whereIn('trasction_stage', $trsactionStage )->get();
        if (!$mongoRecords->isEmpty()) {
            return response()->json([
                "status" => 404,
                "message" => "Mongo records found, data will not be deleted"
            ]);
        }

        $corporateDeleted = corporatesOnBoardingMaster::where('id', $request->id)->delete();
        $whiteListDeleted = WhiteListingCorporatesOnBoardingModel::where('corporates_on_boarding_id', $request->id)->delete();

        if ($corporateDeleted || $whiteListDeleted) {
            return response()->json([
                "status" => 200,
                "message" => "Data deleted successfully"
            ]);
        } else {
            return response()->json([
                "status" => 404,
                "message" => "No data found to delete"
            ]);
        }
    }



    public function getCompanyDomain(request $request) {
        if (!empty($request)) {
            $data = '';
            $domain = $request->domain;
            if (empty($domain)) {
                return response()->json([
                    "status" => false,
                    "message" => "No Data Found"
                ]);
            }



            $data = corporatesOnBoardingMaster::where('company_domain', 'LIKE', "%{$domain}%")->get();

           $data = corporatesOnBoardingMaster::whereRaw("FIND_IN_SET(?, company_domain)", [$domain])->get();


            if ($data->isEmpty()) {
                $data = WhiteListingCorporatesOnBoardingModel::where('email_id', $domain)->get();

                if (!$data->isEmpty()) {
                    $corporateOnBoardingId = $data->first()->corporates_on_boarding_id;

                    $data = CorporatesOnBoardingMaster::join('white_listing_corporates_on_boarding_master as b', 'corporates_on_boarding_master.id', '=', 'b.corporates_on_boarding_id')
                        ->select('corporates_on_boarding_master.*', 'b.*')
                        ->where('corporates_on_boarding_master.id', $corporateOnBoardingId)
                        ->get();
                }
            }

            if ($data->isEmpty()) {
                $updated_email = explode('@', $domain)[1] ?? '';
                $data = corporatesOnBoardingMaster::where('company_domain', 'LIKE', "%{$updated_email}%")->get();
            }

            if ($data->isEmpty()) {
                $data  = corporatesOnBoardingMaster::where('work_email', $domain)->get();
            }

            if (!($data->isEmpty())) {
                return ([
                    "status" => true,
                    "status_code" => 200,
                    "data" => $data
                ]);
            } else {
                return ([
                    "status" => false,
                    "status_code" => 404,
                    "message" => "No Data Found"
                ]);
            }
        }
    }

    public function addWhitelistEmail(Request $request)
    {
        if (!empty($request)) {
            if ($request->has("corporate_id")) {
                $coropearteIdCheck = corporatesOnBoardingMaster::where('id', $request->corporate_id)->first();
                if (empty($coropearteIdCheck)) {
                    return response()->json([
                        "status" => 404,
                        "message" => "corporate_id Not Found"
                    ]);
                }
            }

            $emails = explode(',', $request->email_id);
            $errors = [];
            $successCount = 0;

            foreach ($emails as $email) {
                $email = trim($email);

                try {
                    // Check if the email already exists for the given corporate ID
                    $existingEntry = WhiteListingCorporatesOnBoardingModel::where([
                        'corporates_on_boarding_id' => $request->corporate_id,
                        'email_id' => $email
                    ])->first();

                    // If the entry does not exist, create a new one
                    if (!$existingEntry) {
                        WhiteListingCorporatesOnBoardingModel::create([
                            "corporates_on_boarding_id" => $request->corporate_id,
                            "email_id" => $email,
                            "mobile_no" => $request->mobile_no ?? '',
                            "status" => "Active"
                        ]);
                        $successCount++;
                    } else {
                        $errors[] = [
                            "email" => $email,
                            "error" => "Email already exists for the given corporate ID."
                        ];
                    }
                } catch (\Exception $e) {
                    $errors[] = [
                        "email" => $email,
                        "error" => $e->getMessage()
                    ];
                }
            }

            if (empty($errors)) {
                return response()->json([
                    "status" => 200,
                    "message" => "All emails processed successfully",
                    "processed_emails" => $successCount
                ]);
            } else {
                return response()->json([
                    "status" => 207,
                    "message" => "Some emails failed to process",
                    "processed_emails" => $successCount,
                    "failed_emails" => $errors
                ]);
            }
        }

        return response()->json([
            "status" => 400,
            "message" => "Bad Request"
        ]);
    }

    public function addWhitelistDomain(Request $request)
    {
        if (!empty($request)) {
            $coropearteIdCheck = corporatesOnBoardingMaster::where('id', $request->corporate_id)->first();
            if (empty($coropearteIdCheck)) {
                return response()->json([
                    "status" => 404,
                    "message" => "corporate_id Not Found"
                ]);
            }

            $existingDomains = $coropearteIdCheck->company_domain;

            $existingDomainArray = !empty($existingDomains) ? array_filter(array_map('trim', explode(',', $existingDomains))) : [];

            $newDomains = array_filter(array_map('trim', explode(',', $request->company_domain)));

            $addedDomains = [];
            $existingNewDomains = [];

            foreach ($newDomains as $newDomain) {
                if (!in_array($newDomain, $existingDomainArray)) {
                    $addedDomains[] = $newDomain;
                    $existingDomainArray[] = $newDomain;
                } else {
                    $existingNewDomains[] = $newDomain;
                }
            }

            if (empty($addedDomains)) {
                return response()->json([
                    "status" => 409,
                    "message" => "All specified domains already exist: " . implode(', ', $existingNewDomains)
                ]);
            }

            $coropearteIdCheck->update([
                'company_domain' => implode(',', array_unique($existingDomainArray)),
                'updated_at' => now(),
            ]);

            return response()->json([
                "status" => 200,
                "message" => "New company domains added successfully.",
                "added_domains" => $addedDomains
            ]);
        }

        return response()->json([
            "status" => 400,
            "message" => "Bad Request"
        ]);
    }
    public function getDomain(Request $request) {
        $request->validate([
            'id' => 'required|integer',
        ]);

        $corporate = corporatesOnBoardingMaster::select('company_domain')
                        ->where('id', $request->id)
                        ->first();


        return response()->json([
            'company_domain' => $corporate->company_domain
        ]);
    }

    public function corporateEmailWhitelisting(Request $request) 
    {
        $token = $request->bearerToken();

        if (!validateToken($token)) {
            return response()->json(['message' => 'Invalid or expired token'], 401);
        }
        Log::info('Incoming Request:', $request->all()); 

        try {
            $request->validate([
                'email_id' => ['required', 'email']
            ], [
                'email_id.required' => 'The email field is required.',
                'email_id.email' => 'The email address format is invalid. Please enter a valid email.'
            ]);

            $emailid = $request->email_id;

            $emailcheck = WhiteListingCorporatesOnBoardingModel::where('email_id', $emailid)->first();

            if ($emailcheck) {
                $corporateData = corporatesOnBoardingMaster::select(
                    'id as corporate_id', 'company_name', 'mobile_no',
                    'is_verified_required_to', 'designation', 'is_verified', 'status'
                )->find($emailcheck->corporates_on_boarding_id);

                if ($corporateData) {
                    return response()->json([
                        'status' => true,
                        'message' => 'Corporate onboarding data found.',
                        'data' => $corporateData, 
                    ], 200);
                }

                return response()->json([
                    'status' => false,
                    'message' => 'Corporate onboarding data not found for this email.',
                ], 404);
            } 

            $company_domain = substr(strrchr($emailid, "@"), 1); 

            $corporateData = corporatesOnBoardingMaster::select(
                'id as corporate_id', 'company_name', 'mobile_no',
                    'is_verified_required_to', 'designation', 'is_verified', 'status'
            )
            ->whereRaw("FIND_IN_SET(?, company_domain)", [$company_domain])
            ->orWhere('company_domain', 'LIKE', "%$company_domain%")
            ->first();

            if ($corporateData) {
                return response()->json([
                    'status' => true,
                    'message' => 'Corporate onboarding data found based on email domain.',
                    'data' => $corporateData, 
                ], 200);
            }

            return response()->json([
                'status' => false,
                'message' => 'Email not found in whitelist or company domain does not exist.',
            ], 404);

        } catch (ValidationException $e) {
            return response()->json([
                'status' => false,
                'message' => 'Validation failed.',
                'errors' => $e->errors(),
            ], 400);
        } catch (Exception $e) {
            Log::error('Error in corporateEmailWhitelisting:', ['error' => $e->getMessage()]);
            return response()->json([
                'status' => false,
                'message' => 'An unexpected error occurred. Please try again later.',
            ], 500);
        }
    }

}
