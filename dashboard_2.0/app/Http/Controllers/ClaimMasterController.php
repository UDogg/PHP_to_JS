<?php

namespace App\Http\Controllers;
use App\Models\AccidentCategory;
use App\Models\VehiclePartData;
use App\Models\LicenseType;
use Illuminate\Http\Request;
use App\Models\MongoModel;
use App\Models\StagemasterModel;
use App\Models\substagemaster;
use App\Models\ClaimRaise;
use App\Models\Catastrophy;
use App\Http\Requests\CatastrophyRequest;
use App\Http\Requests\ClaimRequest;
use App\Models\ClaimManagement;
use App\Models\ClaimStageMaster;
use Illuminate\Support\Facades\Auth;
class ClaimMasterController extends Controller
{
    public function dropdown(){
        return response()->json(AccidentCategory::where('status','Y')->get(['id', 'nature_of_accident as label', 'nature_of_accident as value', 'status']));
    }

    public function index()
    {
        return response()->json(AccidentCategory::all());
    }

    public function store(Request $request){
        $request->validate([
            'nature_of_accident'=> 'required|string|unique:accidents,nature_of_accident',
            'status' => ['required', 'in:Y,N'],

        ]);
        $accident = AccidentCategory::create($request->all());
        return response()->json(['message' => 'Accident type added successfully', 'data' => $accident], 201);
    }

    public function update(Request $request, $id)
    {
        $request->validate([
            'nature_of_accident' => 'required|string|unique:accidents,nature_of_accident,' . $id,
            'status' => ['required', 'in:Y,N'],
        ]);

        $accident = AccidentCategory::find($id);
        $accident->update($request->all());

        return response()->json(['message' => 'Accident type updated successfully', 'data' => $accident]);
    }

    public function destroy($id)
    {
        $accident = AccidentCategory::find($id);
        $accident->delete();

        return response()->json(['message' => 'Accident type deleted successfully']);
    }

    //vehicle parts data:

    public function getVehiclePartsData(){
        return response()->json(VehiclePartData::get(['id','vehicle_parts as label','vehicle_parts as value']));
    }

    public function indexData()
    {
        return response()->json(VehiclePartData::all());
    }

    public function storeData(Request $request){
        $request->validate([
            'vehicle_parts'=> 'required|string|unique:vehicle_parts_data,vehicle_parts'

        ]);
        $data = VehiclePartData::create($request->all());
        return response()->json(['message' => 'Parts Of Vehicle added successfully', 'data' => $data], 201);
    }

    public function updateData(Request $request, $id)
    {
        $request->validate([
            'vehicle_parts' => 'required|string|unique:vehicle_parts_data,vehicle_parts,' . $id
        ]);

        $accident = VehiclePartData::find($id);
        $accident->update($request->all());

        return response()->json(['message' => 'Data updated successfully', 'data' => $accident]);
    }

    public function delete($id)
    {
        $accident = VehiclePartData::find($id);
        $accident->delete();

        return response()->json(['message' => 'Data deleted successfully']);
    }

    public function getLicenseDropdown()
    {
        return response()->json(LicenseType::all(['id', 'license_type']));
    }

    public function listLicenseTypes()
    {
        return response()->json(LicenseType::all());
    }

    public function addLicenseType(Request $request)
    {
        $request->validate([
            'license_type' => 'required|string|unique:license_types,license_type',
        ]);

        $license = LicenseType::create($request->all());

        return response()->json(['message' => 'License type added successfully', 'data' => $license], 201);
    }

    public function editLicenseType(Request $request, $id)
    {
        $request->validate([
            'license_type' => 'required|string|unique:license_types,license_type,' . $id,
        ]);

        $license = LicenseType::find($id);
        $license->update($request->all());

        return response()->json(['message' => 'License type updated successfully', 'data' => $license]);
    }
    public function removeLicenseType($id)
    {
        $license = LicenseType::find($id);
        $license->delete();

        return response()->json(['message' => 'License type deleted successfully']);
    }

    public function claimDataSearch(Request $request)
    {
        if (!$request->has('policy_no') && !$request->has('vehicle_registration_number')) {
            return response()->json([
                'error' => 'Either policy_no or vehicle_registration_number is required'
            ], 400);
        }

        $stage = StagemasterModel::where('stage_name', 'Issued')->first(['id', 'sub_stage_name']);
        if (!$stage) {
            return response()->json(['error' => 'Stage not found'], 404);
        }

        $subStageList = explode(',', $stage->sub_stage_name);
        $transactionStages = substagemaster::whereIn('id', $subStageList)->pluck('sub_stage_name')->toArray();

        $query = MongoModel::select('primary_insured_name', 
                                    'policy_no', 
                                    'vehicle_registration_number',
                                    'chassis_number', 
                                    'proposer_mobile', 
                                    'engine_number', 
                                    'company_name',
                                    'vehicle_make',
                                    'vehicle_model',
                                    'vehicle_version',
                                    'policy_start_date',
                                    'policy_end_date')
                            ->whereIn('transaction_stage', $transactionStages);

        $policyNo = $request->input('policy_no');
        $vehicleRegNo = $request->input('vehicle_registration_number');
    
        if (!empty($policyNo) && !empty($vehicleRegNo)) {
            $query->where(function ($q) use ($policyNo, $vehicleRegNo) {
                $q->whereIn('policy_no', (array) $policyNo)
                ->whereIn('vehicle_registration_number', (array) $vehicleRegNo);
            });
        } elseif (!empty($policyNo)) {
            $query->whereIn('policy_no', (array) $policyNo);
        } elseif (!empty($vehicleRegNo)) {
            $query->whereIn('vehicle_registration_number', (array) $vehicleRegNo);

        }

        $data = $query->get();

        if ($data->isEmpty()) {
            return response()->json([
                'return_data' => [],
                'message' => 'No records found'
            ], 404);
        }

        return response()->json([
            'status'=> 200,
            'column_head' => [

                ["header" => "Proposer_Mobile", "accessorKey" => "proposer_mobile", "type" => "string"],
                ["header" => "Vehicle_Registration_Number", "accessorKey" => "vehicle_registration_number", "type" => "string"],
                ["header" => "Insurance_Company", "accessorKey" => "company_name", "type" => "string"],
                ["header" => "Primary_Insured_Name", "accessorKey" => "primary_insured_name", "type" => "string"],
                ["header" => "Policy_No", "accessorKey" => "policy_no", "type" => "string"],
                ["header" => "Vehicle_Make", "accessorKey" => "vehicle_make", "type" => "string"],
                ["header" => "Vehicle_Model", "accessorKey" => "vehicle_model", "type" => "string"],
                ["header" => "Vehicle_Version", "accessorKey" => "vehicle_version", "type" => "string"],
                ["header" => "Policy_Start_Date", "accessorKey" => "policy_start_date", "type" => "string"],
                ["header" => "Policy_End_Date", "accessorKey" => "policy_end_date", "type" => "string"],
                ["header" => "Engine_Number", "accessorKey" => "engine_number", "type" => "string"]

            ],
            'return_data' => $data,
            'message' => 'Records found',
        ]);
    }

    public function createClaim(ClaimRequest $request)
    {
        $user = Auth::user();
        // Generate an 8-digit reference code using time (HHMMSS) + 2 random digits

        $referenceCode = date('His') . rand(10, 99);
        $data = $request->all();
    
        if (isset($data['partOfVehicle']) && is_array($data['partOfVehicle'])) {
            $data['partOfVehicle'] = json_encode($data['partOfVehicle']);
        }

        $data['reference_code'] = $referenceCode;
        $data['claim_status'] = 'claim raised';
        $data['user_id'] = $user->id;
        $claim = ClaimRaise::create($data);
    
        return response()->json([
            'status' => 200,
            'return_data' => $claim,
            'message' => 'Claim created successfully'
        ]);
    }

    public function claimList(Request $request)
    {
        $limit = $request->has('size') ? (int) $request->get('size') : 10;

        $query = ClaimRaise::query();
    

        if ($request->has('claim_number') && !empty($request->input('claim_number'))) {
            $query->where('claim_number', $request->input('claim_number'));
        }
        if ($request->has('policyNo') && !empty($request->input('policyNo'))) {
            $query->where('policyNo', $request->input('policyNo'));
        } 
        if ($request->has('registrationNo') && !empty($request->input('registrationNo'))) {

            $query->where('registrationNo', $request->input('registrationNo'));
        }
        $claims = $query->paginate($limit);
        if ($claims->isEmpty()) {
            return response()->json([
                'status' => 404,
                'message' => 'No records found'
            ]);
        }

        foreach ($claims as $claim) {
            if (!empty($claim->partOfVehicle)) {
                $decodedPart = json_decode($claim->partOfVehicle, true);
                if (is_array($decodedPart)) {
                    $claim->partOfVehicle = implode(', ', $decodedPart);
                }
            }
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                            [
                                "header" => "PolicyNo",
                                "accessorKey" => "policyNo",
                                "type" => "string"
                            ],
                            [
                                "header" => "RegistrationNo",
                                "accessorKey" => "registrationNo",
                                "type" => "string"
                            ],
                            [
                                "header" => "Claim Number",
                                "accessorKey" => "claim_number",
                                "type" => "string"
                            ],
                            [
                                "header" => "Claim_Status",
                                "accessorKey" => "claim_status",
                                "type" => "string"
                            ],
                            [
                                "header" => "Workshop_Name",
                                "accessorKey" => "workShopName",
                                "type" => "string"
                            ],
                            [
                                "header" => "ISO_Code",
                                "accessorKey" => "lsoCode",
                                "type" => "string"
                            ],
                            [
                                "header" => "Workshop_Address",
                                "accessorKey" => "workshopAddress",
                                "type" => "string"
                            ],
                            [
                                "header" => "Workshop_Email",
                                "accessorKey" => "workshopEmail",
                                "type" => "string"
                            ],
                            [
                                "header" => "WorkShop_Contact",
                                "accessorKey" => "workShopContact",
                                "type" => "string"
                            ],
                            
                            [
                                "header" => "Workshop_State",
                                "accessorKey" => "workshopState",
                                "type" => "string"
                            ],
                            [
                                "header" => "Workshop_City",
                                "accessorKey" => "workshopCity",
                                "type" => "string"
                            ],
                            [
                                "header" => "Contact_State",
                                "accessorKey" => "contactState",
                                "type" => "string"
                            ],
                            [
                                "header" => "Contact_City",
                                "accessorKey" => "contactCity",
                                "type" => "string"
                            ],
                            [
                                "header" => "Contact_Pincode",
                                "accessorKey" => "contactPincode",
                                "type" => "string"
                            ],
                            [
                                "header" => "Driver_Name",
                                "accessorKey" => "driverName",
                                "type" => "string"
                            ],
                            [
                                "header" => "Insurer_Address",
                                "accessorKey" => "insurerAddress",
                                "type" => "string"
                            ],
                            [
                                "header" => "Customer_EmailId",
                                "accessorKey" => "customerEmailId",
                                "type" => "string"
                            ],
                            [
                                "header" => "Customer_MobileNo",
                                "accessorKey" => "customerMobileNo",
                                "type" => "string"
                            ],
                            [
                                "header" => "Mobile_No",
                                "accessorKey" => "mobileNo",
                                "type" => "string"
                            ],
                            [
                                "header" => "Intimated_Name",
                                "accessorKey" => "intimatedName",
                                "type" => "string"
                            ],
                            [
                                "header" => "Claim_Intimated_By",
                                "accessorKey" => "claimIntimatedBy",
                                "type" => "string"
                            ],
                            [
                                "header" => "Description_Of_Accident",
                                "accessorKey" => "descriptionOfAccident",
                                "type" => "string"
                            ],
                            [
                                "header" => "Catastrophic_Code",
                                "accessorKey" => "catastrophicCode",
                                "type" => "string"
                            ],
                            [
                                "header" => "Part_Of_Vehicle",
                                "accessorKey" => "partOfVehicle",
                                "type" => "string"
                            ],
                            [
                                "header" => "Date_Of_Accident",
                                "accessorKey" => "dateOfAccident",
                                "type" => "string"
                            ],
                            [
                                "header" => "Place_Of_Accident",
                                "accessorKey" => "placeOfAccident",
                                "type" => "string"
                            ],
                            [
                                "header" => "Accident_State",
                                "accessorKey" => "accidentState",
                                "type" => "string"
                            ],
                            [
                                "header" => "Accident_City",
                                "accessorKey" => "accidentCity",
                                "type" => "string"
                            ],
                            [
                                "header" => "Accident_City_Pincode",
                                "accessorKey" => "accidentCityPincode",
                                "type" => "string"
                            ],
                            [
                                "header" => "Nature_Of_Accident",
                                "accessorKey" => "natureOfAccident",
                                "type" => "string"
                            ],
                            [
                                "header" => "Option",
                                "accessorKey" => "option",
                                "type" => "string"
                            ],
                            
                            [
                                "header" => "Was_Vehicle_Parked",
                                "accessorKey" => "wasVehicleParked",
                                "type" => "string"
                            ],
                            [
                                "header" => "Authorized_Dealer",
                                "accessorKey" => "authorizedDealer",
                                "type" => "string"
                            ],
                            [
                                "header" => "Dealer",
                                "accessorKey" => "dealer",
                                "type" => "string"
                            ],
                            [
                                "header" => "Claim_Created_By",
                                "accessorKey" => "claim_created_by",
                                "type" => "string"
                            ],
                        ],
            'return_data' => $claims->items(),
            'pagination' => [
                            'total_records' => $claims->total(),
                            'per_page' => $claims->perPage(),
                            'current_page' => $claims->currentPage(),
                            'total_pages' => $claims->lastPage(),
                        ],
            'message' => 'Claim list'
        ]);
    }
    
    public function getClaimPolicyDetails(Request $request)
    {
        $request->validate([
            '_id' => 'required|string'
        ]);

        $stage = StagemasterModel::where('stage_name', 'Issued')->first(['id', 'sub_stage_name']);
        if (!$stage) {
            return response()->json(['error' => 'Stage not found'], 404);
        }

        $subStageList = explode(',', $stage->sub_stage_name);
        $transactionStages = substagemaster::whereIn('id', $subStageList)->pluck('sub_stage_name')->toArray();

        $data = MongoModel::where('_id', $request->_id)
            ->whereIn('transaction_stage', $transactionStages)
            ->first(['primary_insured_name', 
                    'policy_no', 
                    'vehicle_registration_number',
                    'chassis_number', 
                    'proposer_mobile', 
                    'engine_number', 
                    'company_name',
                    'vehicle_make',
                    'vehicle_model',
                    'vehicle_version',
                    'policy_start_date',
                    'policy_end_date']);

        if (!$data) {
            return response()->json([
                'message' => 'No record found'
            ], 404);
        }

        return response()->json([
            'status' => 200,
            'return_data' => $data,
            'message' => 'Record found',
        ]);
    }

    public function createCatastrophy(CatastrophyRequest $request) 
    {
        $Data = Catastrophy::updateOrCreate(
            ['id' => $request->id],
            $request->all() 
        );

        $message = $Data->wasRecentlyCreated ? 'Catastrophy created successfully' : 'Catastrophy updated successfully';


        $orderedData = Catastrophy::orderBy('created_at', 'desc')->get();
        return response()->json([
            'status' => 200,
            'return_data' => $orderedData,

            'message' => $message
        ]);
    }

    public function listCatastrophy(Request $request){
        $limit = $request->has('size') ? (int) $request->get('size') : 10;
    

        $listCatastrophy = Catastrophy::orderBY('id', 'desc')->paginate($limit);

    
        if ($listCatastrophy->isNotEmpty()) {
            return response()->json([
                'status' => 200, 
                'column_head' => [
                    [

                        "header" => "Catastrophic_Name",
                        "accessorKey" => "catastrophicName",
                        "type" => "string"
                    ],
                    [
                        "header" => "Catastrophic_Code",
                        "accessorKey" => "catastrophicCode",
                        "type" => "string"
                    ],
                    [
                        "header" => "Catastrophic_Date",
                        "accessorKey" => "catastrophicDate",

                        "type" => "string"
                    ],
                    [
                        "header" => "Catastrophic_Date_Valid_Upto",
                        "accessorKey" => "catastrophicDateValidUpto",
                        "type" => "string"
                    ],
                    [

                        "header" => "Is_Ongoing",
                        "accessorKey" => "isOngoing",
                        "type" => "string"
                    ], 
                    [
                        "header" => "Status",
                        "accessorKey" => "status",
                        "type" => "string"
                    ],

                ],
                'return_data' => $listCatastrophy->items(),
                'pagination' => [
                    'total_records' => $listCatastrophy->total(),
                    'per_page' => $listCatastrophy->perPage(),
                    'current_page' => $listCatastrophy->currentPage(),
                    'total_pages' => $listCatastrophy->lastPage(),
                ],
                'message' => 'Data Found'
            ]);
        } else {
            return response()->json([
                'status' => 404, 
                'message' => 'No Data Found'
            ]);
        }
    }
    
    public function deleteCatastrophy(Request $request) 
    {
        $catastrophy = Catastrophy::find($request->id);
    
        if ($catastrophy) {
            $catastrophy->delete();
            return response()->json([
                'status' => 200,
                'message' => 'Catastrophy deleted successfully'
            ]);
        } else {
            return response()->json([
                'status' => 404,
                'message' => 'Catastrophy not found'
            ]);
        }
    }
    
    public function getClaimId(Request $request)
    {
        $id = $request->input('id'); 

        if (!$id) {
            return response()->json([
                'status' => 400,
                'message' => 'Claim ID is required'
            ], 400);
        }

        $claim = ClaimRaise::find($id);

        if (!$claim) {
            return response()->json([
                'status' => 404,
                'message' => 'Claim not found'
            ], 404);
        }

        $formattedData = [
            [
                "Accident Details" => [
                    "natureOfAccident" => $claim->natureOfAccident,
                    "option" => $claim->option,
                    "accidentState" => $claim->accidentState,
                    "accidentCity" => $claim->accidentCity,
                    "accidentCityPincode" => $claim->accidentCityPincode,
                    "dateOfAccident" => $claim->dateOfAccident,
                    "placeOfAccident" => $claim->placeOfAccident,
                    "descriptionOfAccident" => $claim->descriptionOfAccident,
                    "created_at" => $claim->created_at?->format('Y-m-d'),
                ]
            ],
            [
                "Contact Details" => [
                    "intimatedName" => $claim->intimatedName,
                    "mobileNo" => $claim->mobileNo,
                    "insurerAddress" => $claim->insurerAddress,
                    "driverName" => $claim->driverName,
                    "contactState" => $claim->contactState,
                    "contactCity" => $claim->contactCity,
                    "contactPincode" => $claim->contactPincode,
                ]
            ],
            [
                "Workshop Details" => [
                    "workShopName" => $claim->workShopName,
                    "workshopAddress" => $claim->workshopAddress,
                    "workshopEmail" => $claim->workshopEmail,
                    "workShopContact" => $claim->workShopContact,
                    "workshopState" => $claim->workshopState,
                    "workshopCity" => $claim->workshopCity,
                    "dealer" => $claim->dealer,
                ]
            ]
        ];

        return response()->json([
            'status' => 200,
            'return_data' => $formattedData,
            'message' => 'Claim data retrieved successfully'
        ]);
    }

    public function createClaimManagement(Request $request) 
    {
        if ($request->has('claim_id')) {
            $claimManagement = ClaimManagement::updateOrCreate(
                ['claim_id' => $request->input('claim_id')],
                $request->all()
            );
        } else {
            $claimManagement = ClaimManagement::create($request->all());
        }
    
        if ($request->has('claim_raised_status')) {
            ClaimRaise::updateOrInsert(
                ['id' => $claimManagement->claim_id], 
                ['claim_status' => $request->input('claim_raised_status'),
                'claim_number' => $request->input('claimNumber') 
                ]
            );
        }
    
        return response()->json([
            'status' => 200,
            'return_data' => $claimManagement,
            'message' => 'Claim created successfully'
        ]);
    }

    public function getClaimManagement(Request $request)
    {
        $claim_id = $request->input('claim_id');
    
        if (!$claim_id) {
            return response()->json([
                'status' => 400,
                'message' => 'ID is required'
            ]);
        }
    
        $claim = ClaimManagement::where('claim_id', $claim_id)->first();
    
        if (!$claim) {
            return response()->json([
                'status' => 404,
                'message' => 'No records found for the given ID'
            ]);
        }
    
        $formattedClaim = [
            'claim_raised_status' => $claim->claim_raised_status];
        $sections = [
            'Intimation Details' => [
                'intimationDate' => $claim->intimationDate,
                'claimNumber' => $claim->claimNumber,
            ],
            'Surveyor Deputation' => [
                'surveyorName' => $claim->surveyorName,
                'surveyorMobileNo' => $claim->surveyorMobileNo,
                'surveyorEmail' => $claim->surveyorEmail,
                'surveyorDeputationDateTime' => $claim->surveyorDeputationDateTime,
            ],
            'Surveyor Completion' => [
                'surveyorDate' => $claim->surveyorDate,
                'surveyorTime' => $claim->surveyorTime,
            ],
            'Work Approval' => [
                'workDateTime' => $claim->workDateTime,
                'workEstimatedAmount' => $claim->workEstimatedAmount,
                'workClaimApprovalAmount' => $claim->workClaimApprovalAmount,
            ],
            'Delivery Order' => [
                'deliveryClaimType' => $claim->deliveryClaimType,
                'deliveryInvoiceAmount' => $claim->deliveryInvoiceAmount,
                'deliveryClaimApprovalAmount' => $claim->deliveryClaimApprovalAmount,
                'deliveryDifferenceAmount' => $claim->deliveryDifferenceAmount,
                'deliveryCompulsoryDeductibles' => $claim->deliveryCompulsoryDeductibles,
                'deliveryVoluntaryExcess' => $claim->deliveryVoluntaryExcess,
                'deliveryDepreciation' => $claim->deliveryDepreciation,
                'deliveryOthers' => $claim->deliveryOthers,
            ],
            'Settled' => [
                'settledPayeeName' => $claim->settledPayeeName,
                'settledPaymentDate' => $claim->settledPaymentDate,
                'settledPaymentAmount' => $claim->settledPaymentAmount,
                'settledReferenceNumber' => $claim->settledReferenceNumber,
                'settledModeOfPayment' => $claim->settledModeOfPayment,
            ],
            'Rejection' => [
                'rejectionReason' => $claim->rejectionReason,
            ],
            'Withdrawal' => [
                'withDrawAgree' => $claim->withDrawAgree,
                'withDrawalReason' => $claim->withDrawalReason,
            ],
        ];
    
        // Filter out sections where all values are null
        $filteredSections = array_filter($sections, function ($values) {
            return array_filter($values, fn($value) => !is_null($value));
        });

        $formattedClaim += $filteredSections;
        return response()->json([
            'status' => 200,
            'return_data' => $formattedClaim,
            'message' => 'Claim details retrieved successfully'
        ]);
    }

    public function stagesList(Request $request)
    {
        return response()->json(ClaimStageMaster::get(['id', 'stage_name as label', 'stage_name as value']));
    }

    public function getCatastrophy(Request $request)
    {

        return response()->json(Catastrophy::where('status','Active')->get(['id','catastrophicName as label','catastrophicName as value']));

    }
}
