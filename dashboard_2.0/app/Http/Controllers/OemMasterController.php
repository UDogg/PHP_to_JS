<?php

namespace App\Http\Controllers;

use App\Exports\AllDataExport;
use App\Exports\MispBranchExport;
use App\Jobs\ExportLargeExcel;
use App\Models\DataExportLog;
use App\Models\ExcelDownloadLog;
use App\Models\MispBranch;
use App\Models\MispMaster;
use App\Models\OemMaster;
use App\Models\OemMasterData;
use Illuminate\Http\Request;
use Illuminate\Support\Carbon;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use Illuminate\Validation\Rule;
use Maatwebsite\Excel\Facades\Excel;

class OemMasterController extends Controller
{
    protected $Auth;
    public function __construct()
    {
        $this->Auth = Auth::user();
    }
    public function index()
    {
        $oem_data = OemMaster::all();

        $get_oem_name = OemMaster::select('oem_name')->get();

        return view('oem_master', compact('oem_data', 'get_oem_name'));
    }
    public function store(Request $request)
    {

        $rules = [
            'oem_name' => ['required', 'string'],

        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                ],
                500
            );
        } else {

            $oem_data = new OemMaster();
            $oem_data->oem_name = $request->oem_name;


            $oem_data->save();

            if ($oem_data->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $oem_data,
                    'message' => 'OEM Data Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }
    }
    public function storeMisp(Request $request)
    {

        $rules = [
            'misp_name' => ['required', 'string'],
                    'oem_name' => ['required', 'string'],
                    'pan_number' => ['required', 'string'],
                    'gstin' => ['required', 'string'],
                    'dealer_code' => ['required', 'string'],
                    'branch_name' => ['required', 'string'],
                    'address' => ['required', 'string'],
                    'head_office' => ['required', 'string', 'unique:oem_masters,head_office'],
                    'misp_code' => ['required', 'string'],
                    'pin_code' => ['required', 'string'],
                    'city' => ['required', 'string'],
                    'state' => ['required', 'string'],
                    'mob_no' => ['required', 'numeric'],
                    'email' => ['required', 'email'],
                    'status' => ['required', 'string'],

        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                ],
                500
            );
        } else {

            $misp_data = new OemMaster();
            $misp_data->misp_name = $request->misp_name;
            $misp_data->oem_name = $request->oem_name;
            $misp_data->pan_number = $request->pan_number;
            $misp_data->zone = $request->zone;
            $misp_data->gstin = $request->gstin;
            $misp_data->dealer_code = $request->dealer_code;


            $misp_data->save();

            if ($misp_data->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $misp_data,
                    'message' => 'OEM Data Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }
    }
    public function storeBranch(Request $request)
    {
        $submissionStage = $request->input('submission_stage', 1);
        $recordId = $request->input('id');
        $oemName = $request->input('oem_name');

        $branch = null;


        if ($recordId) {
            $branch = OemMaster::find($recordId);
            if (!$branch) {
                return response()->json([
                    'status' => 404,
                    'message' => 'Record not found'
                ], 404);
            }
        }


        if (!$branch && $submissionStage == 1) {
            $branch = new OemMaster();
        }


        $rules = [];
        switch ($submissionStage) {
            case 1:

                $rules = ['oem_name' => ['required', 'string']];
                break;

            case 2:

                $rules = [
                    'misp_name' => ['required', 'string'],
                    'pan_number' => ['required', 'string'],
                    'zone' => ['required', 'string'],
                    'gstin' => ['required', 'string'],
                    'dealer_code' => ['required', 'string'],
                    'head_office' => ['required', 'string', 'unique:oem_masters,head_office,' . ($branch ? $branch->id : null)],
                    'misp_code' => ['required', 'string'],
                    'pin_code' => ['required', 'string'],
                    'city' => ['required', 'string'],
                    'state' => ['required', 'string'],
                    'mob_no' => ['required', 'numeric'],
                    'email' => ['required', 'email'],
                    'status' => ['required', 'string'],
                ];
                break;

            case 3:

                $rules = [
                    'branch_name' => ['required', 'string'],
                    'address' => ['required', 'string'],
                ];
                break;

            default:
                return response()->json([
                    'status' => 400,
                    'message' => 'Invalid submission stage',
                ], 400);
        }

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Invalid request data',
                'errors' => $validator->errors(),
            ], 500);
        }


        if ($submissionStage == 1) {
            $branch->oem_name = $request->oem_name;
        }

        if ($submissionStage == 2) {
            $branch->fill($request->only([
                'misp_name', 'pan_number', 'zone', 'gstin', 'dealer_code',
                'head_office', 'misp_code', 'pin_code', 'city', 'state',
                'mob_no', 'email', 'status'
            ]));
        }

        if ($submissionStage == 3) {
            $branch->branch_name = $request->branch_name;
            $branch->address = $request->address;
        }

        if ($branch->save()) {
            return response()->json([
                'status' => 200,
                'return_data' => $branch,
                'message' => 'OEM Data Saved Successfully',
            ], 200);
        } else {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Failed to save OEM data',
            ], 500);
        }
    }
    public function destroy(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $oem_data = OemMaster::where('id', $request->id)->first();

        if ($oem_data) {
            $oem_data->delete();
            return response()->json(['message' => 'OEM Data deleted successfully']);
        } else {
            return response()->json(['message' => 'Tag Data not found or already deleted']);
        }
    }
    public function updateMisp(Request $request)
    {

        $request->validate([
            'misp_name' => ['required', 'string'],
            'oem_name' => ['required', 'string'],
            'pan_number' => ['required', 'string'],
            'gstin' => ['required', 'string'],
            'dealer_code' => ['required', 'string'],
            'branch_name' => ['required', 'string'],
            'address' => ['required', 'string'],
            'head_office'=>['required', 'string'],
            'misp_code' => ['required', 'string'],
            'pin_code' => ['required', 'string'],
            'city' => ['required', 'string'],
            'state' => ['required', 'string'],
            'mob_no' => ['required', 'numeric'],
            'email' => ['required', 'email'],
            'status' => ['required', 'string'],
        ]);


        $misp_data = OemMaster::find($request->id);

        if (!$misp_data) {
            return response()->json(['message' => 'misp_data not found!'], 404);
        }


        $misp_data->misp_name = $request->misp_name;
        $misp_data->oem_name = $request->oem_name;
        $misp_data->pan_number = $request->pan_number;
        $misp_data->zone = $request->zone;
        $misp_data->gstin = $request->gstin;
        $misp_data->dealer_code = $request->dealer_code;
        $misp_data->branch_name = $request->branch_name;
        $misp_data->address = $request->address;
        $misp_data->head_office = $request->head_office;
        $misp_data->misp_code = $request->misp_code;
        $misp_data->pin_code = $request->pin_code;
        $misp_data->city = $request->city;
        $misp_data->state = $request->state;
        $misp_data->mob_no = $request->mob_no;
        $misp_data->email = $request->email;
        $misp_data->status = $request->status;

        $misp_data->save();

        return response()->json([
            'status' => 200,
            'return_data' => $misp_data,
            'message' => 'misp_data updated successfully!']);
    }
    public function show(Request $request) {

        $oem_data = OemMaster::all();
        return response()->json($oem_data);
    }
    public function getOemData(Request $request)
    {
        $oem_data = OemMaster::select("oem_name")->get();
        // dd($oem_data);
        return response()->json($oem_data);
    }
    public function getMispData(Request $request)
    {
        $misp_data = OemMaster::select("misp_name")->get();
        // dd($misp_data);
        return response()->json($misp_data);
    }
    public function getHoData(Request $request)
    {

        $rules = [
            'head_office' => ['required', 'string'],
        ];

        // Validate the incoming request
        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                ],
                500
            );
        }

        // If validation passes, fetch the address from the database or another source
        $headOffice = $request->input('head_office');


        $hoData = OemMaster::select('address')
            ->where('head_office', $headOffice)
            ->first();

        if ($hoData) {

            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [
                        'head_office' => $headOffice,
                        'address' => $hoData->address,
                    ],
                    'message' => 'Data retrieved successfully',
                ],
                200
            );
        } else {

            return response()->json(
                [
                    'status' => 404,
                    'return_data' => [],
                    'message' => 'Head office not found',
                ],
                404
            );
        }
    }
    public function getbranch(Request $request) {

        $rules = [
            'misp_name' => ['required', 'string'],
        ];

        // Validate the incoming request
        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                ],
                500
            );
        }
        $branch = $request->input('misp_name');
        // If validation passes, fetch the address from the database or another source
        $branch_name = OemMaster::select('address')
            ->where('head_office', $branch)
            ->first();

        if ($branch_name) {

            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [
                        'head_office' => $branch,
                        'address' => $branch_name->address,
                    ],
                    'message' => 'Data retrieved successfully',
                ],
                200
            );
        } else {

            return response()->json(
                [
                    'status' => 404,
                    'return_data' => [],
                    'message' => 'Head office not found',
                ],
                404
            );
        }
    }

    // Store Only OEM Data in OEM Master
    public function storeOem(Request $request)
    {
        $createPermission = "OEM Onboarding.edit";
        if(!$this->Auth->can($createPermission))
        {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $rules = [
            'oem_name' => ['required', 'string'],

        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                ],
                500
            );
        } else {

            $oem_data = new OemMasterData();
            $oem_data->oem_name = $request->oem_name;

            $oem_data->save();

            if ($oem_data->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $oem_data,
                    'message' => 'oem_data Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }
    }
    // List OEM Master Data
    public function indexOem(Request $request)
    {
        $listingPermission = "OEM Onboarding.view";
        if(!$this->Auth->can($listingPermission))
        {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

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
        $query = OemMasterData::query();

        //search filter
        if (!empty($search)) {
            $query->where('oem_name', 'LIKE', "%{$search}%")
                ->orWhere('oem_id', 'LIKE', "%{$search}%");
        }
        $queryColumns = ['oem_id', 'oem_name']; // Columns to filter
        $model = OemMasterData::class;
        if ($request->input('export', false)) {
            $dataCount = $query->count();
            $maxAllowedCount = config('DATA.EXPORT.LIMIT');
            $headings = ['Oem Id', 'Oem Name', 'created_at', 'updated_at', 'deleted_at'];
            if($dataCount > $maxAllowedCount)
            {
                $log = ExcelDownloadLog::insert([
                    'user_id' => $this->Auth->id,
                    'request' => json_encode($request->all()),
                    'status' => '0',
                    'created_at' => Carbon::now(),
                    'source' => 'Oem Data Export'
                ]);
                $random = rand(1, 10000000);
                $filename = 'Data/OEM'.$random.'.xlsx';
                ExportLargeExcel::dispatch($model,$queryColumns,$headings,$request->all(),$this->Auth->id,'OEMDataExport',$filename)->onQueue('LargeExcelExports');
                return response()->json([
                    'status' => 200,
                    'message' => 'Data is to large to download. Added to Queue You will get this file later in job list  ',
                ]);
            }
            else
            {
                $export = new AllDataExport($request,$model, $headings,$queryColumns);
                $random = Str::random(10);
                $filePath = 'Data/OEM'.$random.'.xlsx';
                Excel::store($export, $filePath, 'public');
                $downloadLink = Storage::disk('public')->url($filePath);
                ExcelDataExportLog($this->Auth->id, $filePath, 'OEM', 'completed',$request->all());
                return response()->json([
                    'status' => 200,
                    'message' => 'Excel file generated successfully',
                    'link' => $downloadLink,
                ]);
            }
        }

    // pagination
        if ($pagination) {
            $oem_data = $query->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $oem_data->lastPage();
            $totalCount = $oem_data->total();
            $prevPage = $oem_data->previousPageUrl() ? $page - 1 : null;
            $nextPage = $oem_data->nextPageUrl() ? $page + 1 : null;
            $oem_data = $oem_data->toArray()['data'];


            return response()->json([
                'status' => 200,
                'data' => $oem_data,
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
            $oem_data = $query->get();
            $totalCount = $oem_data->count();

            return response()->json([
                'status' => 200,
                'data' => $oem_data,
                'total' => $totalCount,
            ]);
        }

    }
    // Update OEM Master Data
    public function updateOem(Request $request)
    {

        $createPermission = "OEM Onboarding.edit";
        if(!$this->Auth->can($createPermission))
        {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $request->validate([
            'oem_name' => ['required', 'string'],
        ]);


        $oem_data = OemMasterData::find($request->id);

        if (!$oem_data) {
            return response()->json(['message' => 'oem_data not found!'], 404);
        }


        $oem_data->oem_name = $request->oem_name;

        $oem_data->save();

        return response()->json([
            'status' => 200,
            'return_data' => $oem_data,
            'message' => 'oem_data updated successfully!']);
    }
    // Get Oem_name List
    public function getOemList(Request $request)
    {
        $oem_data = OemMasterData::select("oem_name")->get();

        return response()->json($oem_data);
    }
    // Store MISP Master Data
    public function storeMispData(Request $request)
    {

        $rules = [
            'misp_name' => ['required', 'string'],
            'oem_name' => ['required', 'string'],
            'pan_number' => ['required', 'string'],
            'gstin' => ['required', 'string'],
            'address' => ['required', 'string'],
            'head_office' => ['required', 'string', 'unique:oem_masters,head_office'],
            'misp_code' => ['required', 'string'],
            'pin_code' => ['required', 'string'],
            'city' => ['required', 'string'],
            'state' => ['required', 'string'],
            'mob_no' => ['required', 'numeric'],
            'email' => ['required', 'email'],
            'status' => ['required', 'string'],
            'oem_id' => [
                'required',
                'numeric',
                Rule::unique('misp_masters')->where(function ($query) use ($request) {
                    return $query->where('dealer_code', $request->dealer_code)
                                ->where('pan_number', $request->pan_number);
                })
            ],
        ];

        $messages = [
            'misp_name.required' => 'The MISP name is required.',
            'oem_name.required' => 'The OEM name is required.',
            'oem_id.unique' => 'The combination of OEM ID, Dealer Code, and PAN number has already been taken.',
            'pan_number.required' => 'The PAN number is required.',
            'gstin.required' => 'The GSTIN is required.',

            'address.required' => 'The address is required.',
            'head_office.required' => 'The head office field is required.',
            'head_office.unique' => 'The head office has already been taken.',
            'misp_code.required' => 'The MISP code is required.',
            'pin_code.required' => 'The pin code is required.',
            'city.required' => 'The city is required.',
            'state.required' => 'The state is required.',
            'mob_no.required' => 'The mobile number is required.',
            'mob_no.numeric' => 'The mobile number must be a numeric value.',
            'email.required' => 'The email address is required.',
            'email.email' => 'The email address must be a valid email.',
            'status.required' => 'The status is required.',
        ];

        // Validate the request data
        $validator = Validator::make($request->all(), $rules, $messages);

        if ($validator->fails()) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => $validator->errors()->first(),
            ], 500);
        }


        $misp_data = new MispMaster();
        $misp_data->misp_name = $request->misp_name;
        $misp_data->oem_name = $request->oem_name;
        $misp_data->oem_id = $request->oem_id;
        $misp_data->pan_number = $request->pan_number;
        $misp_data->zone = $request->zone;
        $misp_data->gstin = $request->gstin;
        $misp_data->dealer_code = $request->dealer_code;
        $misp_data->address = $request->address;
        $misp_data->head_office = $request->head_office;
        $misp_data->misp_code = $request->misp_code;
        $misp_data->pin_code = $request->pin_code;
        $misp_data->city = $request->city;
        $misp_data->state = $request->state;
        $misp_data->mob_no = $request->mob_no;
        $misp_data->email = $request->email;
        $misp_data->status = $request->status;

        // Save the data
        if ($misp_data->save()) {
            return response()->json([
                'status' => 200,
                'return_data' => $misp_data,
                'message' => 'MISP Data Created Successfully',
            ], 200);
        } else {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Failed to save MISP data',
            ], 500);
        }
    }
    // List MISP Master Data
    public function ListMisp(Request $request)
{
    $listingPermission = "MISP Onboarding.view";
    if(!$this->Auth->can($listingPermission))
    {
        return response()->json([
            'status' => 403,
            'message' => 'You do not have permission to access this resource.',
        ], 403);
    }
    $request->validate([
        'page' => 'integer',
        'perPageRecords' => 'integer',
        'pagination' => 'boolean',
        'export' => 'boolean',
        'search' => 'nullable|string',
        'oem_id' => 'nullable|integer'
    ]);

    $pagination = $request->input('pagination', true);
    $page = $request->input('page', 1);
    $perPageRecords = $request->input('perPageRecords', 10);
    $search = $request->input('search', '');
    $oem_id = $request->input('oem_id', null);
    $query = MispMaster::query();

    // Filter by oem_id if provided
    if (!empty($oem_id)) {
        $query->where('oem_id', $oem_id);
    }

    // Apply search filter
    if (!empty($search)) {
        $query->where(function ($q) use ($search) {
            $q->where('misp_id', 'LIKE', "%{$search}%")
                ->orWhere('misp_name', 'LIKE', "%{$search}%")
                ->orWhere('oem_id', 'LIKE', "%{$search}%")
                ->orWhere('oem_name', 'LIKE', "%{$search}%")
                ->orWhere('mob_no', 'LIKE', "%{$search}%")
                ->orWhere('email', 'LIKE', "%{$search}%");

        });
    }
    $queryColumns = ['misp_id', 'oem_name','misp_name','misp_code','pan_number','gstin','zone','dealer_code','pin_code','city','state','mob_no','email','status','created_at','updated_at','address','head_office','oem_id'];
    $model = MispMaster::class;
    if ($request->input('export', false)) {
        $dataCount = $query->count();
        $maxAllowedCount = config('DATA.EXPORT.LIMIT');
        $headings = [
            'Misp Id', 'Oem Name', 'Misp Name', 'Misp Code', 'Pan Number', 'Gstin',
            'Zone', 'Dealer Code', 'Pin Code', 'City', 'State', 'Mobile No', 'Email', 'Status','Created At','Updated At','Address','Head Office','Oem Id'
        ];
        if($dataCount > $maxAllowedCount)
        {
            $log = ExcelDownloadLog::insert([
                'user_id' => $this->Auth->id,
                'request' => json_encode($request->all()),
                'status' => '0',
                'created_at' => Carbon::now(),
                'source' => 'Oem Data Export'
            ]);
            $random = rand(1, 10000000);
            $filename = 'Data/Misp'.$random.'.xlsx';
             ExportLargeExcel::dispatch($model,$headings,$request->all(),$this->Auth->id,'OEMDataExport',$filename,$queryColumns)->onQueue('LargeExcelExports'); // --NEW

            return response()->json([
                'status' => 200,
                'message' => 'Data is to large to download. Added to Queue You will get this file later in job list  ',
            ]);
        }
        else
        {
            $export = new AllDataExport($request,$model, $headings,$queryColumns);
            $random = Str::random(10);
            $filePath = 'Data/Misp'.$random.'.xlsx';
            Excel::store($export, $filePath, 'public');
            $downloadLink = Storage::disk('public')->url($filePath);
            ExcelDataExportLog($this->Auth->id, $filePath, 'OEM', 'completed',$request->all());
            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }
    }
    // Handle export functionality

    if ($pagination) {
        $misp_data = $query->paginate($perPageRecords, ['*'], 'page', $page);
        $lastPage = $misp_data->lastPage();
        $totalCount = $misp_data->total();
        $prevPage = $misp_data->previousPageUrl() ? $page - 1 : null;
        $nextPage = $misp_data->nextPageUrl() ? $page + 1 : null;
        $misp_data = $misp_data->toArray()['data'];


        return response()->json([
            'status' => 200,
            'data' => $misp_data,
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
        $misp_data = $query->get();
        $totalCount = $misp_data->count();

        return response()->json([
            'status' => 200,
            'data' => $misp_data,
            'total' => $totalCount,
        ]);
    }
}

    // Get Misp_name List
    public function getMispListData(Request $request)
    {
        $oem_data = MispMaster::select("misp_name")->get();

        return response()->json($oem_data);
    }

    // Delete MISP Master Data
    public function destroyMisp(Request $request)
    {
        $deletePermission = "MISP Onboarding.delete";
        if(!$this->Auth->can($deletePermission))
        {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to delete this resource.',
            ], 403);
        }

        $request->validate([
            'id' => 'required|exists:misp_masters,misp_id', // Make sure oem_id exists in the table
        ]);

        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $oem_data = MispMaster::where('misp_id', $request->id)->first();

        if ($oem_data) {
            $oem_data->delete();
            return response()->json(['message' => 'MISP deleted successfully']);
        } else {
            return response()->json(['message' => 'MISP not found or already deleted']);
        }
    }
     // update MISP Master Data
    public function updateMispData(Request $request)
    {
        $updatePermission = "MISP Onboarding.edit";
        if(!$this->Auth->can($updatePermission))
        {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to update this resource.',
            ], 403);
        }

        $misp_data = MispMaster::find($request->misp_id);

        if (!$misp_data) {
            return response()->json(['message' => 'misp_data not found!'], 404);
        }

            $misp_data->misp_name = $request->misp_name;
            $misp_data->oem_name = $request->oem_name;
            $misp_data->pan_number = $request->pan_number;
            $misp_data->zone = $request->zone;
            $misp_data->gstin = $request->gstin;
            $misp_data->dealer_code = $request->dealer_code;
            $misp_data->address = $request->address;
            $misp_data->head_office = $request->head_office;
            $misp_data->misp_code = $request->misp_code;
            $misp_data->pin_code = $request->pin_code;
            $misp_data->city = $request->city;
            $misp_data->state = $request->state;
            $misp_data->mob_no = $request->mob_no;
            $misp_data->email = $request->email;
            $misp_data->status = $request->status;
            $misp_data->save();

        return response()->json([
            'status' => 200,
            'return_data' => $misp_data,
            'message' => 'misp_data updated successfully!']);
    }
    public function destroyOem(Request $request)
    {
        $request->validate([
            'id' => 'required|exists:oem_master_data,oem_id', // Make sure oem_id exists in the table
        ]);

        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $oem_data = OemMasterData::where('oem_id', $request->id)->first();

        if ($oem_data) {
            $oem_data->delete();
            return response()->json(['message' => 'OEM deleted successfully']);
        } else {
            return response()->json(['message' => 'OEM not found or already deleted']);
        }
    }

     // Store Only Branch in Branch Master
     public function storeMispBranch(Request $request)
     {
         $inactiveResponse = checkUserActivity($request);
         if ($inactiveResponse) {
             return $inactiveResponse;
         }
         $rules = [
            'oem_name' => ['required', 'string'],
            'misp_name' => ['required', 'string'],
            'branchDetails' => ['required', 'array'],
            'branchDetails.*.branch_name' => ['required', 'string'],
            'branchDetails.*.address' => ['required', 'string'],
            'branchDetails.*.code' => ['required', 'string'],
            'branchDetails.*.zone' => ['required', 'string'],
            'branchDetails.*.email' => ['required', 'email'],
            'branchDetails.*.mobile_number' => ['required', 'string', 'min:10'],
            'branchDetails.*.pin_code' => ['required', 'string', 'min:6'],
            'branchDetails.*.city' => ['required', 'string'],
            'branchDetails.*.state' => ['required', 'string'],
            'branchDetails.*.status' => ['required'],

        ];

         $validator = Validator::make($request->all(), $rules);

         if ($validator->fails()) {
             return response()->json(
                 [
                     'status' => 500,
                     'return_data' => [],
                     'message' => 'Invalid request data',
                     'errors' => $validator->errors(), // Detailed validation errors

                 ],
                 500
             );
         } else {
            $branches = [];

            foreach ($request->branchDetails as $branch) {
                $misp_branch = new MispBranch();
                $misp_branch->oem_id = $request->oem_id;
                $misp_branch->oem_name = $request->oem_name;
                $misp_branch->misp_id = $request->misp_id;
                $misp_branch->misp_name = $request->misp_name;
                $misp_branch->branch_name = $branch['branch_name'];
                $misp_branch->address = $branch['address'];
                $misp_branch->city = $branch['city'];
                $misp_branch->state = $branch['state'];
                $misp_branch->pin_code = $branch['pin_code'];
                $misp_branch->code = $branch['code'];

                $misp_branch->zone = $branch['zone'];
                $misp_branch->email = $branch['email'];
                $misp_branch->mobile_number = $branch['mobile_number'];
                $misp_branch->status = $branch['status'];
                $misp_branch->save();
                $branches[] = $misp_branch;
            }

            return response()->json([
                'status' => 200,
                'return_data' => $branches,
                'message' => 'MISP Branches Created Successfully',
            ], 200);
         }
     }

    public function updateMispBranch(Request $request)
    {
        // Check user activity
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $rules = [
            'oem_id' => ['required', 'integer'],
            'oem_name' => ['required', 'string'],
            'misp_id' => ['required', 'integer'],
            'misp_name' => ['required', 'string'],
            'branchDetails' => ['required', 'array'],
            'branchDetails.*.id' => ['required', 'integer'],
            'branchDetails.*.branch_name' => ['required', 'string'],
            'branchDetails.*.address' => ['required', 'string'],
            'branchDetails.*.code' => ['required', 'string'],
            'branchDetails.*.zone' => ['required', 'string'],
            'branchDetails.*.email' => ['required', 'email'],
            'branchDetails.*.mobile_number' => ['required', 'string', 'min:10'],
            'branchDetails.*.pin_code' => ['required', 'string', 'min:6'],
            'branchDetails.*.city' => ['required', 'string'],
            'branchDetails.*.state' => ['required', 'string'],
            'branchDetails.*.status' => ['required'],
        ];


        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                    'errors' => $validator->errors(),
                ],
                500
            );
        }


        $updatedBranches = [];


        foreach ($request->branchDetails as $branch) {

            $misp_branch = MispBranch::where('branch_id', $branch['id'])->first();
            if ($misp_branch) {

                $misp_branch->oem_id = $request->oem_id;
                $misp_branch->oem_name = $request->oem_name;
                $misp_branch->misp_id = $request->misp_id;
                $misp_branch->misp_name = $request->misp_name;
                $misp_branch->branch_name = $branch['branch_name'];
                $misp_branch->address = $branch['address'];
                $misp_branch->city = $branch['city'];
                $misp_branch->state = $branch['state'];
                $misp_branch->pin_code = $branch['pin_code'];
                $misp_branch->code = $branch['code'];
                $misp_branch->zone = $branch['zone'];
                $misp_branch->email = $branch['email'];
                $misp_branch->mobile_number = $branch['mobile_number'];
                $misp_branch->status = $branch['status'];


                $misp_branch->save();


                $updatedBranches[] = $misp_branch;
            }
        }


        return response()->json([
            'status' => 200,
            'return_data' => $updatedBranches,
            'message' => 'MISP Branches Updated Successfully',
        ], 200);
    }


    public function destroyMispBranch(Request $request)
    {
        $request->validate([
            'id' => 'required|exists:misp_branches,branch_id', // Make sure oem_id exists in the table
        ]);

        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $misp_branch = MispBranch::where('branch_id', $request->id)->first();

        if ($misp_branch) {
            $misp_branch->delete();
            return response()->json(['message' => 'Branch deleted successfully']);
        } else {
            return response()->json(['message' => 'Branch not found or already deleted']);
        }
    }


    public function mispBranchList(Request $request)
    {
        $request->validate([
            'page' => 'integer',
            'perPageRecords' => 'integer',
            'pagination' => 'boolean',
            'export' => 'boolean',
            'search' => 'nullable|string',
            'oem_id' => 'nullable|integer',
            'misp_id' => 'nullable|integer',
        ]);

        $pagination = $request->input('pagination', true);
        $page = $request->input('page', 1);
        $perPageRecords = $request->input('perPageRecords', 10);
        $search = $request->input('search', '');
        $oemId = $request->input('oem_id');
        $mispId = $request->input('misp_id');

        $query = MispBranch::query();

        // Filter by oem_id if provided
        if (!empty($oemId)) {
            $query->where('oem_id', $oemId);
        }

        // Filter by misp_id if provided
        if (!empty($mispId)) {
            $query->where('misp_id', $mispId);
        }

        // Apply search filter
        if (!empty($search)) {
            $query->where(function($query) use ($search) {
                $query->where('misp_id', 'LIKE', "{$search}%")
                    ->orWhere('misp_name', 'LIKE', "{$search}%")
                    ->orWhere('oem_id', 'LIKE', "{$search}%")
                    ->orWhere('oem_name', 'LIKE', "{$search}%")
                    ->orWhere('branch_id', 'LIKE', "{$search}%")
                    ->orWhere('branch_name', 'LIKE', "{$search}%");
            });
        }
        $queryColumns = ['misp_id', 'oem_name','misp_name','misp_code','pan_number','gstin','zone','dealer_code','pin_code','city','state','mob_no','email','status','created_at','updated_at','address','head_office','oem_id'];
        $model = MispBranch::class;

        if ($request->input('export', false)) {
            $dataCount = $query->count();
            $maxAllowedCount = config('DATA.EXPORT.LIMIT');
            $headings = ['Branch Id', 'Oem Id', 'Oem Name', 'Misp Id', 'Misp Name', 'branch_name', 'address', 'City', 'State', 'Pin Code', 'Code', 'created_at', 'updated_at', 'deleted_at', 'Zone', 'Mobile Number', 'Email', 'Status'];
            if($dataCount > $maxAllowedCount)
            {
                $log = ExcelDownloadLog::insert([
                    'user_id' => $this->Auth->id,
                    'request' => json_encode($request->all()),
                    'status' => '0',
                    'created_at' => Carbon::now(),
                    'source' => 'Oem Data Export'
                ]);
                $random = rand(1, 10000000);
                $filename = 'Data/MispBranches'.$random.'.xlsx';
                ExportLargeExcel::dispatch($model,$headings,$queryColumns,$request->all(),$this->Auth->id,'MispBranchExport',$filename)->onQueue('LargeExcelExports');
                return response()->json([
                    'status' => 200,
                    'message' => 'Data is to large to download. Added to Queue You will get this file later in job list  ',
                ]);
            }
            else
            {
                $export = new AllDataExport($request,$model, $headings,$queryColumns);
                $random = Str::random(10);
                $filePath = 'Data/MispBranches'.$random.'.xlsx';
                Excel::store($export, $filePath, 'public');
                $downloadLink = Storage::disk('public')->url($filePath);
                ExcelDataExportLog($this->Auth->id, $filePath, 'OEM', 'completed',$request->all());
                return response()->json([
                    'status' => 200,
                    'message' => 'Excel file generated successfully',
                    'link' => $downloadLink,
                ]);
            }
        }

        if ($pagination) {
            $misp_branch = $query->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $misp_branch->lastPage();
            $totalCount = $misp_branch->total();
            $prevPage = $misp_branch->previousPageUrl() ? $page - 1 : null;
            $nextPage = $misp_branch->nextPageUrl() ? $page + 1 : null;
            $misp_branch = $misp_branch->toArray()['data'];


            return response()->json([
                'status' => 200,
                'data' => $misp_branch,
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
            $misp_branch = $query->get();
            $totalCount = $misp_branch->count();

            return response()->json([
                'status' => 200,
                'data' => $misp_branch,
                'total' => $totalCount,
            ]);
        }
    }



}
