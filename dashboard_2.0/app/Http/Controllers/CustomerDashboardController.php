<?php

namespace App\Http\Controllers;

use App\Models\CustomerPolicyExpire;
use App\Models\MongoModel;
use Illuminate\Http\Request;
use App\Models\customerVehicle;
use App\Models\ReferenceCustomerLead;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;

use Illuminate\Support\Facades\File;
use App\Http\Requests\RefCustomerValidations;
use App\Models\User;
use Maatwebsite\Excel\Facades\Excel;
use App\Exports\ReferenceCustomerLeadExport;
use Illuminate\Support\Facades\Storage;
class CustomerDashboardController extends Controller
{
    public function store(Request $request)
    {
        $user= Auth::user();
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $rules = [

            'vehicle_id' => ['required', 'string'],
            'fuel_id' => ['required', 'string'],
            'reg_no' => ['required', 'string', 'unique:customer_vehicles,reg_no'],
            'date_of_registration' => ['required', 'string'],
            'make' => ['required', 'string'],
            'model' => ['required', 'string'],
            'variant' => ['required', 'string'],
            'status' => ['required'],
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

            $customer_vehicle = new customerVehicle();
            $customer_vehicle->vehicle_id = $request->vehicle_id; // Store total minutes in the database
            $customer_vehicle->user_id = $user->id;
            $customer_vehicle->fuel_id = $request->fuel_id;
            $customer_vehicle->reg_no = $request->reg_no;
            $customer_vehicle->date_of_registration = $request->date_of_registration;
            $customer_vehicle->make = $request->make;
            $customer_vehicle->model = $request->model;
            $customer_vehicle->variant = $request->variant;
            $customer_vehicle->versionName = $request->versionName;
            $customer_vehicle->status = $request->status;

            $customer_vehicle->save();

            if ($customer_vehicle->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $customer_vehicle,
                    'message' => 'Customer Vehicle Created Successfully',
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

    public function customVehicleList(Request $request){
        $user= Auth::user();
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        if ($request->vehicle_id) {
            // For a single vehicle, check if the result is null
            $customer_vehicle = customerVehicle::leftJoin('lob_master', 'lob_master.id', '=', 'customer_vehicles.vehicle_id')
                ->select('customer_vehicles.*', 'lob_master.lob as vehicle_type')
                ->where('customer_vehicles.vehicle_id', $request->vehicle_id)
                ->first();
        
            // Check if no vehicle was found (null check)
            if (!$customer_vehicle) {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Customer Vehicle not found'
                    ],
                    500
                );
            }
        } else {
            // For multiple vehicles, check if the collection is empty
            // $customer_vehicle = customerVehicle::leftJoin('lob_master', 'lob_master.id', '=', 'customer_vehicles.vehicle_id')
            //     ->select('customer_vehicles.*', 'lob_master.lob as vehicle_type')
            //     ->where('customer_vehicles.user_id', $user->id)
            //     ->get();

            $customer_vehicle = CustomerPolicyExpire::leftJoin('lob_master', 'lob_master.id', '=', 'customer_policy_expire.lob_id')
                ->select('customer_policy_expire.*', 'lob_master.lob as vehicle_type')
                ->where('customer_policy_expire.customer_id', $user->id)
                ->get();
 
            // Check if the collection is empty
            if ($customer_vehicle->isEmpty()) {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Customer Vehicles not found'
                    ],
                    500
                );
            }
        }
        
        return response()->json(
            [
                'status' => 200,
                'return_data' => $customer_vehicle,
                'message' => 'Customer Vehicle List'
            ],
            200
        );

    }
    public function update(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $customer_vehicle = customerVehicle::findOrFail($request->customer_vehicle_id);
        if ( $customer_vehicle) {
            $customer_vehicle->update($request->all());

            return response()->json(
                [
                    'status' => 200,
                    'return_data' => $customer_vehicle,
                    'message' => 'vehicle Updated Successfully',
                ],
                200
            );
        } else {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'vehicle not found',
                ],
                500
            );
        }
    }
    public function destroy(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $customerVehicleData = customerVehicle::where('customer_vehicle_id', $request->customer_vehicle_id)->first();
        if ($customerVehicleData) {
            $customerVehicleData->delete();
            return response()->json([ 'status' => 200,'return_data' => $customerVehicleData,'message' => 'Template deleted successfully']);
        } else {

            return response()->json([ 'status' => 500,'return_data' => [],'message' => 'Template not found or already deleted']);
        }

    }

    public function viewQuotesUrl(Request $request)
    {
        $reg_no = $request->reg_no;
        $user = Auth::user();

        $query = MongoModel::select('quote_url')->where('user_id', $user->id);
        if (!empty($reg_no)) {
            $query->where('vehicle_registration_number', $reg_no);
        }

        $data = $query->get();

        if ($data->isEmpty()) {
            return response()->json([
                'message' => 'Data not found',
            ], 404);
        }

        $quoteUrl = $data->first()->quote_url;
        return redirect($quoteUrl);
    }

    public function referenceCustomerLead(RefCustomerValidations $request)
    {
        $createdBy = null;

        if ($request->filled('reference_code')) {
            $user = User::where('share_code', $request->reference_code)->first();

            if ($user) {
                $createdBy = $user->id; 
            }
        }  
        $data = ReferenceCustomerLead::updateOrCreate(
            ['id' => $request->id],    
            [
                'name' => $request->name,
                'mobile' => $request->mobile,
                'email' => $request->email,
                'created_by' => $createdBy 
            ]
        );

        $message = $request->id ? 'Data Updated Successfully' : 'Data Stored Successfully';

        return response()->json([
            'status' => 200,
            'return_data' => $data,
            'message' => $message
        ]);
    }

    public function getreferenceCustomerLead(Request $request)
    {
        $limit = $request->has('size') ? (int) $request->get('size') : 10;

        $user = Auth::user();
        if (!$user) {
            return response()->json([
                'status' => 401,
                'message' => 'Unauthorized access. Please log in.'
            ], 401);
        }
    
        $query = ReferenceCustomerLead::query();
    
        if ($user->is_admin === "Y" && $user->usertype === "1")
        {
        } else {
            $UserHierarchyArray = [];
    
            $getUserHierarchyData = getUserLowerHierarchy($user->id, $user->userType->id);
    
            $UserHierarchyArray[] = $user->id;
    
            if (is_iterable($getUserHierarchyData)) {
                foreach ($getUserHierarchyData as $value) {
                    $UserHierarchyArray[] = $value['id'] ?? $value->id;
                }
            }
    
            $query->whereIn('created_by', $UserHierarchyArray);
        }

        if ($request->filled('name')) {
            $query->where('name', 'LIKE', "%{$request->name}%");
        }
        
        if ($request->filled('email')) {
            $query->where('email', 'LIKE', "%{$request->email}%");
        }

        if ($request->filled('mobile')) {
            $query->where('mobile', 'LIKE', "%{$request->mobile}%");
        }

        $referenceQuery = $query->orderBy('created_at', 'desc')->paginate($limit);

        $formattedData = $referenceQuery->map(function ($item) {
            return [
                'name' => $item->name,
                'email' => $item->email,
                'mobile' => $item->mobile,
                'created_at' => $item->created_at?->format('Y-m-d'), 
            ];
        });
    
        return response()->json([
            'status' => 200,
            'column_head' => [
                ["header" => "Name", "accessorKey" => "name", "type" => "string"],
                ["header" => "Email", "accessorKey" => "email", "type" => "string"],
                ["header" => "Mobile", "accessorKey" => "mobile", "type" => "string"],
                ["header" => "Created At", "accessorKey" => "created_at", "type" => "datetime"],
            ],
            'return_data' => $formattedData,
            'pagination' => [
                'total_records' => $referenceQuery->total(),
                'per_page' => $referenceQuery->perPage(),
                'current_page' => $referenceQuery->currentPage(),
                'total_pages' => $referenceQuery->lastPage(),
            ],
            'message' => 'Data Fetched Successfully'
        ]);
    }

    public function exportReferenceCustomer(Request $request)
    {
        $fileName = 'Reference_Customer_' . now()->format('Y_m_d_H_i_s') . '.xlsx';
        $filePath = 'ref_customer_reports/' . $fileName;
        $reportsDirectory = storage_path('app/public/ref_customer_reports/');

        if (!File::exists($reportsDirectory)) {
            File::makeDirectory($reportsDirectory, 0755, true);
        }

        $data = ReferenceCustomerLead::all();

        Excel::store(new ReferenceCustomerLeadExport($data), $filePath, 'public');

        $fileUrl = Storage::disk('public')->url($filePath);

        return response()->json([
            'status' => 200,
            'file_url' => $fileUrl,
            'message' => 'Report Generated Successfully'
        ]);
    }

}
