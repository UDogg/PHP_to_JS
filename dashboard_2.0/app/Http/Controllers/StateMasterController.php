<?php

namespace App\Http\Controllers;

use App\Exports\AllDataExport;
use App\Models\cityMaster;
use App\Models\pincodeMaster;
use App\Models\stateMaster;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;
use Maatwebsite\Excel\Facades\Excel;

class StateMasterController extends Controller
{
    public function stateList(Request $request)
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
        $query = stateMaster::query();

        //search filter
        if (!empty($search)) {
            $query->where('state_id', 'LIKE', "%{$search}%")
                ->orWhere('state_name', 'LIKE', "%{$search}%")
                ->orWhere('state_code', 'LIKE', "%{$search}%");

        }

        if ($request->input('export', false)) {

            $headings = ['state_id',  'state_name','state_code','created_at','updated_at','deleted_at'];
            $queryColumns = ['state_id', 'state_name', 'state_code'];


            $export = new AllDataExport($request, stateMaster::class, $headings, $queryColumns);


            $filePath = 'Data/States.xlsx';
            Excel::store($export, $filePath, 'public');


            $downloadLink = Storage::disk('public')->url($filePath);

            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }
        if ($pagination) {
            $state_data = $query->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $state_data->lastPage();
            $totalCount = $state_data->total();
            $prevPage = $state_data->previousPageUrl() ? $page - 1 : null;
            $nextPage = $state_data->nextPageUrl() ? $page + 1 : null;
            $state_data = $state_data->toArray()['data'];

            return response()->json([
                'status' => 200,
                'data' => $state_data,
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

            $state_data = stateMaster::all();
            $totalCount = $state_data->count();


            return response()->json([
                'status' => 200,
                'data' => $state_data,
                'total' => $totalCount,
            ]);
        }

    }
    public function storeState(Request $request)
    {

        $rules = [
            'state_name' => ['required', 'string', 'unique:state_masters,state_name'],
            'state_code' => ['required', 'string', 'unique:state_masters,state_code']
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

            $state_data = new stateMaster();
            $state_data->state_name = $request->state_name;
            $state_data->state_code = $request->state_code;

            $state_data->save();

            if ($state_data->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $state_data,
                    'message' => 'State Created Successfully',
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
    public function updateState(Request $request)
    {

        $request->validate([
            'state_name' => ['required', 'string'],
            'state_code' => ['required', 'string'],
        ]);


        $state_data = stateMaster::find($request->id);

        if (!$state_data) {
            return response()->json(['message' => 'State not found!'], 404);
        }

        $state_data->state_name = $request->state_name;
        $state_data->state_code = $request->state_code;
        $state_data->save();

        return response()->json([
            'status' => 200,
            'return_data' => $state_data,
            'message' => 'State updated successfully!']);
    }
    public function destroyState(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $state_data = stateMaster::where('state_id', $request->id)->first();

        if ($state_data) {
            $state_data->delete();
            return response()->json(['message' => 'State deleted successfully']);
        } else {
            return response()->json(['message' => 'State not found or already deleted']);
        }
    }

    public function cityList(Request $request)
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
        $query = cityMaster::query();

        //search filter
        if (!empty($search)) {
            $query->where('city_id', 'LIKE', "%{$search}%")
                ->orWhere('state_id', 'LIKE', "%{$search}%")
                ->orWhere('city_name', 'LIKE', "%{$search}%")
                ->orWhere('zone_id', 'LIKE', "%{$search}%");
        }

        if ($request->input('export', false)) {

            $headings = ['city_id',  'zone_id','state_id','city_name','created_at','updated_at','deleted_at'];
            $queryColumns = ['column_name_1', 'column_name_2'];


            $export = new AllDataExport($request, cityMaster::class, $headings, $queryColumns);


            $filePath = 'Data/City.xlsx';
            Excel::store($export, $filePath, 'public');


            $downloadLink = Storage::disk('public')->url($filePath);

            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }
        if ($pagination) {
            $city_data = $query->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $city_data->lastPage();
            $totalCount = $city_data->total();
            $prevPage = $city_data->previousPageUrl() ? $page - 1 : null;
            $nextPage = $city_data->nextPageUrl() ? $page + 1 : null;
            $city_data = $city_data->toArray()['data'];

            return response()->json([
                'status' => 200,
                'data' => $city_data,
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

            $city_data = cityMaster::all();
            $totalCount = $city_data->count();


            return response()->json([
                'status' => 200,
                'data' => $city_data,
                'total' => $totalCount,
            ]);
        }

    }
    public function storeCity(Request $request)
    {

        $rules = [
            'zone_id' => ['numeric'],
            'state_id' => ['numeric'],
            'city_name' => ['required', 'string']

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

            $city_data = new cityMaster();
            $city_data->zone_id = $request->zone_id;
            $city_data->state_id = $request->state_id;
            $city_data->city_name = $request->city_name;

            $city_data->save();

            if ($city_data->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $city_data,
                    'message' => 'State Created Successfully',
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
    public function updateCity(Request $request)
    {

        $request->validate([
            'zone_id' => ['numeric'],
            'state_id' => ['numeric'],
            'city_name' => ['required', 'string']
        ]);


        $city_data = cityMaster::find($request->id);

        if (!$city_data) {
            return response()->json(['message' => 'City not found!'], 404);
        }

            $city_data->zone_id = $request->zone_id;
            $city_data->state_id = $request->state_id;
            $city_data->city_name = $request->city_name;
            $city_data->save();

        return response()->json([
            'status' => 200,
            'return_data' => $city_data,
            'message' => 'City updated successfully!']);
    }
    public function destroyCity(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $city_data = cityMaster::where('city_id', $request->id)->first();

        if ($city_data) {
            $city_data->delete();
            return response()->json(['message' => 'City deleted successfully']);
        } else {
            return response()->json(['message' => 'City not found or already deleted']);
        }
    }
    public function storePinCode(Request $request)
    {

        $rules = [
            'pincode' => ['numeric','unique:pincode_masters,pincode','digits:6','regex:/^[1-9][0-9]{5}$/'],


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

            $pincode_data = new pincodeMaster();
            $pincode_data->pincode = $request->pincode;
            $pincode_data->country_code = $request->country_code;
            $pincode_data->state_id = $request->state_id;
            $pincode_data->city_id = $request->city_id;
            $pincode_data->area = $request->area;
            $pincode_data->latitude = $request->latitude;
            $pincode_data->longitude = $request->longitude;
            $pincode_data->geospatial_accuracy = $request->geospatial_accuracy;
            $pincode_data->sequence = $request->sequence;


            $pincode_data->save();

            if ($pincode_data->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $pincode_data,
                    'message' => ' Pincode Added Successfully',
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

    public function pincodeList(Request $request)
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
        $search = $request->input('search','');

        $query = pincodeMaster::query();

        if ($search) {
            $query->where('pincode_id', 'LIKE', "%{$search}%")
                ->orWhere('pincode', 'LIKE', "%{$search}%")
                ->orWhere('country_code','LIKE',"%{$search}%")
                ->orWhere('state_id','LIKE',"%{$search}%")
                ->orWhere('city_id','LIKE',"%{$search}%");

        }

        if ($request->input('export', false)) {

            $headings = ['pincode_id',  'pincode','country_code','state_id','city_id','area','latitude','longitude','geospatial_accuracy','sequence','created_at','updated_at','deleted_at'];
            $queryColumns = ['pincode_id', 'pincode','country_code','state_id','city_id'];


            $export = new AllDataExport($request, pincodeMaster::class, $headings, $queryColumns);


            $filePath = 'Data/Pincode.xlsx';
            Excel::store($export, $filePath, 'public');


            $downloadLink = Storage::disk('public')->url($filePath);

            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }
        if ($pagination) {
            $pincode_data = $query->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $pincode_data->lastPage();
            $totalCount = $pincode_data->total();
            $prevPage = $pincode_data->previousPageUrl() ? $page - 1 : null;
            $nextPage = $pincode_data->nextPageUrl() ? $page + 1 : null;
            $pincode_data = $pincode_data->toArray()['data'];

            return response()->json([
                'status' => 200,
                'data' => $pincode_data,
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

            $pincode_data = pincodeMaster::all();
            $totalCount = $pincode_data->count();


            return response()->json([
                'status' => 200,
                'data' => $pincode_data,
                'total' => $totalCount,
            ]);
        }
    }

    public function updatePincode(Request $request)
    {
        $request->validate([
            'pincode' => ['numeric','unique:pincode_masters,pincode','digits:6','regex:/^[1-9][0-9]{5}$/'],
        ]);


        $pincode_data = pincodeMaster::find($request->id);

        if (!$pincode_data) {
            return response()->json(['message' => 'City not found!'], 404);
        }

        $pincode_data->pincode = $request->pincode;
        $pincode_data->country_code = $request->country_code;
        $pincode_data->state_id = $request->state_id;
        $pincode_data->city_id = $request->city_id;
        $pincode_data->area = $request->area;
        $pincode_data->latitude = $request->latitude;
        $pincode_data->longitude = $request->longitude;
        $pincode_data->geospatial_accuracy = $request->geospatial_accuracy;
        $pincode_data->sequence = $request->sequence;
        $pincode_data->save();

        return response()->json([
            'status' => 200,
            'return_data' => $pincode_data,
            'message' => 'Pincode updated successfully!']);
    }
    public function destroyPincode(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $pincode_data = pincodeMaster::where('pincode_id', $request->id)->first();

        if ($pincode_data) {
            $pincode_data->delete();
            return response()->json(['message' => 'Pincode deleted successfully']);
        } else {
            return response()->json(['message' => 'Pincode not found or already deleted']);
        }
    }

    public function fetchCity(Request $request)
    {
        try {

            $request->validate([
                'pincode' => 'required|digits:6|regex:/^[1-9][0-9]{5}$/',
            ]);

            $pincode = $request->input('pincode');


            $result = pincodeMaster::
                join('city_masters', 'pincode_masters.city_id', '=', 'city_masters.city_id')
                ->join('state_masters', 'pincode_masters.state_id', '=', 'state_masters.state_id')
                ->where('pincode_masters.pincode', $pincode)
                ->select('city_masters.city_id', 'city_masters.city_name', 'state_masters.state_id', 'state_masters.state_name')
                ->first();


            if ($result) {
                return response()->json([
                    'status' => 200,
                    'city_id' => $result->city_id,
                    'city_name' => $result->city_name,
                    'state_id' => $result->state_id,
                    'state_name' => $result->state_name
                ]);
            } else {
                return response()->json([
                    'message' => 'City and State not found for the provided pincode.'
                ], 500);
            }

        } catch (\Illuminate\Validation\ValidationException $e) {

            return response()->json([
                'errors' => $e->errors(),
            ], 422);
        }
    }
}
