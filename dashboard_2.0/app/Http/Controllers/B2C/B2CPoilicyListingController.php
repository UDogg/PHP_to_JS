<?php

namespace App\Http\Controllers\B2C;

use App\Http\Controllers\Controller;
use App\Models\MongoModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;

class B2CPoilicyListingController extends Controller
{
    public function b2cPoilicyListing(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'vehicle_registration_number' => 'required',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'errors' => $validator->errors()
            ], 422);
        }

        $auth = Auth::user();

        if ($auth->usertype != 4) { 
            return response()->json([
                'status' => false,
                'message' => 'Unauthorized access',
            ], 403);
        }
        $page = $request->input('page', 1);
        $perPage = $request->input('size', 10);
        $searchTerm = $request->input('vehicle_registration_number', '');

        $match = [];
        
        $utmParameter = activeRoleCodeMappingUser();
        if (!empty($utmParameter)) {
            foreach ($utmParameter as $key => $value) {
                if($key=='utm_medium') $key='utm_media';
                
                $valueArr = explode(',',$value);
                
                if(count($valueArr)>1)
                    $match['broker_' . $key] = ['$in' => $valueArr];
                else
                    $match['broker_' . $key] = $value;
            }
        } else {
            return response()->json([
                'status' => false,
                'message' => 'No UTM parameters found',
            ], 400);
        }
      
        $query = MongoModel::query();
        // $match['vehicle_registration_number'] = $request->vehicle_registration_number;

        foreach ($match as $key => $value) {
            if (!empty($value)) {
                $query->where($key, $value);
            }
        }

        if (!empty($searchTerm)) {
            $query->where(function ($q) use ($searchTerm) {
                $q->orWhere('trace_id', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('vehicle_registration_number', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('proposer_name', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('proposer_mobile', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('proposer_emailid', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('vehicle_registration_number', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('policy_no', 'regex', '/' . $searchTerm . '/i')
                    ->orWhere('sum_assured', 'regex', '/' . $searchTerm . '/i');
            });
        }
        
        $column_head = $this->B2CPolicyListingColumHead();
        $selectColumns = array_column($column_head, 'accessorKey');
        $selectColumns []='proposal_url';
        $selectColumns []='quote_url';
        $query->select($selectColumns);

        $results = $query->paginate($perPage);

        $transformedData = $this->FormattingB2CListing($results, $page, $perPage);

        if (!empty($results)) {
            return response()->json([
                'status' => 200,
                'column_head' => $column_head,
                'return_data' => $transformedData,
                'pagination' => [
                    'total_records' => $results->total(),
                    'total_pages' => $results->lastPage(),
                    'current_page' => $results->currentPage(),
                    'per_page' => $results->perPage(),
                ],
            ]);
        } else {
            return response()->json([
                'status' => 500,
                'message' => "No Data Found",
                'return_data'=>[]
            ]);
        }
    }

    private function B2CPolicyListingColumHead(){
        $column_head = [
            ["header" => "SR NO", "accessorKey" => "sr_no", "isActions" => false],
            ["header" => "Policy Days", "accessorKey" => "policy_tenture_days", "isActions" => false],
            ["header" => "Trace id", "accessorKey" => "trace_id", "isActions" => false],
            ["header" => "Customer Name", "accessorKey" => "proposer_name", "isActions" => false],
            ["header" => "Mobile No.", "accessorKey" => "proposer_mobile", "isActions" => false],
            ["header" => "Email Id", "accessorKey" => "proposer_emailid", "isActions" => false],
            ["header" => "Vehicle Registration Number", "accessorKey" => "vehicle_registration_number", "isActions" => false],
            ["header" => "Policy type", "accessorKey" => "policy_type", "isActions" => false],
            ["header" => "Insurance Name", "accessorKey" => "company_name", "isActions" => false],
            ["header" => "Premium Amount", "accessorKey" => "premium_amount", "isActions" => false],
            ["header" => "Policy issued Date", "accessorKey" => "policy_start_date", "isActions" => false],
            ["header" => "policy_end_date", "accessorKey" => "policy_end_date", "isActions" => false],
            ["header" => "pincode", "accessorKey" => "pincode", "isActions" => false],
            ["header" => "Policy No", "accessorKey" => "policy_no", "isActions" => false],
            ["header" => "Sum Assured", "accessorKey" => "sum_assured", "isActions" => false],
            ["header" => "Business Type", "accessorKey" => "business_type", "isActions" => false],
            ["header" => "section", "accessorKey" => "section", "isActions" => false],
            ["header" => "Ckyc Status", "accessorKey" => "ckyc_status", "isActions" => false],
            ["header" => "Seller Name", "accessorKey" => "seller_name", "isActions" => false],
            ["header" => "Seller Mobile", "accessorKey" => "seller_mobile", "isActions" => false],
            ["header" => "Seller Type", "accessorKey" => "seller_type", "isActions" => false],
            ["header" => "Seller Username", "accessorKey" => "seller_username", "isActions" => false],
            ["header" => "Product Name", "accessorKey" => "product_name", "isActions" => false],
            ["header" => "Is Offline Entry", "accessorKey" => "is_offline_entry", "isActions" => false],
            ["header" => "Reporting Employee", "accessorKey" => "reporting_employee", "isActions" => false],
            ["header" => "Transaction Stage", "accessorKey" => "transaction_stage", "isActions" => false],

        ];

        return $column_head;

    }

    private function FormattingB2CListing($results, $page, $perPage)
    {
        return $results->map(function ($item,$index) use($page, $perPage) {

            if (isset($item->proposal_url)) {
                    $common_redirect_url = $item->proposal_url;
                }
                if (isset($item->quote_url)) {
                    $common_redirect_url = $item->quote_url;
                }

            return [
                'sr_no' =>  ($page - 1) * $perPage + ($index + 1),
                'policy_tenture_days' => $item->policy_tenture_days ?? '',
                'trace_id' => $item->trace_id ?? '',
                'proposer_name' => $item->proposer_name ?? '',
                'proposer_mobile' => $item->proposer_mobile ?? '',
                'proposer_emailid' => $item->proposer_emailid ?? '',
                'vehicle_registration_number' => $item->vehicle_registration_number ?? '',
                'product_name' => $item->product_name ?? '',
                'policy_type' => $item->policy_type ?? '',
                'company_name' => $item->company_name ?? '',
                'premium_amount' => $item->premium_amount ?? 0,
                'policy_start_date' => $item->policy_start_date ?? null,
                'policy_end_date' => $item->policy_end_date ?? null,
                'pincode' => $item->pincode ?? '',
                'policy_no' => $item->policy_no ?? '',
                'sum_assured' => $item->sum_assured ?? '0',
                'business_type' => $item->business_type ?? '',
                'section' => $item->section ?? '',
                'ckyc_status' => $item->ckyc_status ?? '',
                'seller_name' => $item->seller_name ?? '',
                'seller_mobile' => $item->seller_mobile ?? '',
                'seller_type' => $item->seller_type ?? '',
                'seller_username' => $item->seller_username ?? '',
                'is_offline_entry' => isset($item->is_offline_entry) ? (string) $item->is_offline_entry : '0',
                'reporting_employee' => $item->reporting_employee ?? '',
                'common_redirect_url' => $common_redirect_url ?? '',
                'id' => (string) $item->_id,
            ];
        })->values();

    }


}
