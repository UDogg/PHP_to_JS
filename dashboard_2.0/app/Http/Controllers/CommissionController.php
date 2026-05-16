<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use Carbon\Carbon;

class CommissionController extends Controller
{

    public function vehicleType(Request $request)
    {
        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "lob_master",
            "fieldSlug"=> "lob_master",
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $lob = $this->getMastersFromBrocore($payload);
        
        return response()->json([
            'status' => 200,
            'data' => $lob,
            'message' => 'Vehicle sub types fetched successfully.',
        ]);
        
    }

    public function vehicleSubType(Request $request)
    {
        $lob = $request->lob;

        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "vehicle_sub_type",
            "fieldSlug"=> "vehicle_sub_type",
            "lobId"=> $lob,
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $subTypes = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $subTypes,
            'message' => 'Vehicle sub types fetched successfully.',
        ]);
    }


    public function rto(Request $request)
    {
        $rto_text = $request->rto_text;

        if($rto_text != ''){
            $payload = [
                "page"=> 1,
                "size"=> 10,
                "masterSlug"=> "master_rto",
                "fieldSlug"=> "master_rto",
                "lobId"=> "",
                "data"=> [
                    "rto" => $rto_text
                ],
                "isSmartSearch"=> "Y",
                "token"=> "5554545"
            ];
    
        }else{
            $payload = [
                "page"=> 1,
                "size"=> 10,
                "masterSlug"=> "master_rto",
                "fieldSlug"=> "master_rto",
                "lobId"=> "",
                "isSmartSearch"=> "",
                "token"=> "5554545"
            ];
    
        }

        $rto = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $rto,
            'message' => 'RTO fetched successfully.',
        ]);

    }

    public function state(Request $request)
    {
        $state_text = $request->state_text;

        if($state_text != ''){
            $payload = [
                "page"=> 1,
                "size"=> 10,
                "masterSlug"=> "master_state",
                "fieldSlug"=> "master_state",
                "lobId"=> "",
                "data"=> [
                    "state_name" => $state_text
                ],
                "isSmartSearch"=> "Y",
                "token"=> "5554545"
            ];
        }else{
            $payload = [
                "page"=> 1,
                "size"=> 10,
                "masterSlug"=> "master_state",
                "fieldSlug"=> "master_state",
                "lobId"=> "",
                "isSmartSearch"=> "",
                "token"=> "5554545"
            ];
        }


        $state = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $state,
            'message' => 'States fetched successfully.',
        ]);
    }

    public function city(Request $request)
    {
        $city_text = $request->city_text;
        $state_id = $request->state_id;

        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "master_city",
            "fieldSlug"=> "master_city",
            "lobId"=> "",
            "data"=> [
                "state_id" => $state_id
            ],
            "token"=> "5554545"
        ];


        $city = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $city,
            'message' => 'City fetched successfully.',
        ]);

    }

    public function businessType(Request $request)
    {

        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "transaction_type_master",
            "fieldSlug"=> "transaction_type_master",            
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $businessType = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $businessType,
            'message' => 'Records fetched successfully.',
        ]);
    }

    public function policyType(Request $request)
    {
        $payload = [
            "page"=> 1,
            "size"=> 100,
            "masterSlug"=> "business_type_master",
            "fieldSlug"=> "business_type_master",
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $policyType = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $policyType,
            'message' => 'Records fetched successfully.',
        ]);
    }   

    public function vehicleMake(Request $request)
    {
       $manf_name = $request->make;
       $lob = $request->lob;
        if($lob=='2'){
            $slug='car_manufacturer';
        }elseif($lob=='3'){
            $slug='bike_manufacturer';
        }elseif($lob=='5'){
            $slug = 'gcv_manufacturer';
        }elseif($lob=='6'){
            $slug = 'pcv_manufacturer';
        }elseif($lob=='57'){
            $slug = 'misc_manufacturer';
        }
        $payload = [
            "page"=> 1,
            "size"=> 500,
            "masterSlug"=> $slug,
            "fieldSlug"=> $slug,
            "lobId"=> "",
            // "data"=> [
            //     "manf_name" => $manf_name
            // ],
            // "isSmartSearch"=> "Y",
            "token"=> "5554545"
        ];

        $vehicleMake = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $vehicleMake,
            'message' => 'Records fetched successfully.',
        ]);
    }

    public function vehicleModel(Request $request)
    {
        $payload = [
            "lobid"=> $request->lob,
            "manufacturer_id"=> $request->make_id,
        ];

        $url = 'https://demoapibrokex.fynity.in/field_category_master/get-model';

        $vehicleModel = Http::post($url, $payload)->json();
        // dd($url,$payload,$vehicleModel);
        return response()->json([
            'status' => 200,
            'data' => $vehicleModel,
            'message' => 'Records fetched successfully.',
        ]); 
        
    }

    public function fuelType(Request $request)
    {
        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "fuel_types",
            "fieldSlug"=> "fuel_types",
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $fuelType = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $fuelType,
            'message' => 'Records fetched successfully.',
        ]);
    }

    public function insuranceCompanyMaster(Request $request)
    {

        $payload = [
            "page"=> 1,
            "size"=> 100,
            "masterSlug"=> "master_company",
            "fieldSlug"=> "master_company",
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $insuranceCompanyMaster = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $insuranceCompanyMaster,
            'message' => 'Records fetched successfully.',
        ]);
    }

    public function seatingCapacity(Request $request)
    {
        $lob = $request->lob;
        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "seating_capacity",
            "fieldSlug"=> "seating_capacity",
            "lobId"=> $lob,
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $seatingCapacity = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $seatingCapacity,
            'message' => 'Records fetched successfully.',
        ]);
    }
    public function noOfWheels(Request $request)
    {
        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "number_of_wheels_",
            "fieldSlug"=> "number_of_wheels_",
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $noOfWheelsRange = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $noOfWheelsRange,
            'message' => 'Records fetched successfully.',
        ]);
    }

    public function gvwRange(Request $request)
    {
        $payload = [
            "page"=> 1,
            "size"=> 10,
            "masterSlug"=> "gvw_range",
            "fieldSlug"=> "gvw_range",
            "lobId"=> "",
            "isSmartSearch"=> "",
            "token"=> "5554545"
        ];

        $gvwRange = $this->getMastersFromBrocore($payload);

        return response()->json([
            'status' => 200,
            'data' => $gvwRange,
            'message' => 'Records fetched successfully.',
        ]);
    }

    public function getMastersFromBrocore($payload)
    {
        $url = 'https://demoapibrokex.fynity.in/get_data';
        // $url = 'https://uatapibrokex.fynity.in/get_data';
        $masterResponse = Http::post($url, $payload)->json();
        // dd($url,$payload,$masterResponse);
        if(array_key_exists('data',$masterResponse)){
            return $masterResponse['data'];
        }else{
            return $masterResponse;
        }
        
    }


    public function brokerageCalculation(Request $request)
    {
        $fields = [
            // 'vehicle_sub_type' => 'vehicle_sub_type',
            // 'business_type'    => 'policyType',
            // 'policy_type'      => 'businessType',
            // 'fuel_type'        => 'fuelType',
            // 'rto'              => 'rto',
            
            // 'model'            => 'model',
            // 'state'            => 'rtostate',
        ];
        $fieldsValue = [
            // 'make'             => 'make',
        ];
        
        if($request->date_for_commission)
            $filterDate = Carbon::createFromFormat('d/m/Y', $request->date_for_commission);


        $fieldName = [];
        $filterValue = [];
        
        foreach ($fields as $requestKey => $dbColumnName) {
            if (!empty($request->$requestKey) && !empty($request->$requestKey['value'])) {
        
                $fieldName[] = $dbColumnName;
                $filterValue[] = $request->$requestKey['value'];
            }
        }

        foreach ($fieldsValue as $requestKey => $dbColumnName) {
            if (!empty($request->$requestKey) && !empty($request->$requestKey['label'])) {
        
                $fieldName[] = $dbColumnName;
                $filterValue[] = $request->$requestKey['label'];
            }
        }

        $vehicle_type = $request->vehicle_type['value'];

        $companyId = [0];
        if($request->insurer_name){
            $insurer_values = array_column($request->insurer_name, 'value');
            $companyId = $insurer_values;    
        }

        $url = 'https://demoapibrokex.fynity.in/brokerage_Configurator/brokerage-filter';
        $payload =[
            "lobId"=> $vehicle_type,
            "companyId"=> $companyId,
            "filterValue"=> $filterValue,
            "fieldName"=> $fieldName,
            "pageSize"=> 1000,
            "pageNumber"=> 0
        ];
        
        $masterResponse = Http::post($url, $payload)->json();
        // dd($url,$payload,$masterResponse);
        if($request->date_for_commission){
            $filteredData = collect($masterResponse['data'])->filter(function ($item) use ($filterDate) {
    
                $start = Carbon::parse($item['effectiveStartDate'])->startOfDay();
                $end   = Carbon::parse($item['effectiveEndDate'])->endOfDay();
                // dd($start,$end,$filterDate);
                return $filterDate->between($start, $end);
            });
            $masterResponse = $filteredData;    
        }

        // $masterResponse.map()
        // dd($url,$payload,$masterResponse);
        // if(array_key_exists('data',$masterResponse)){
        //     return $masterResponse['data'];
        // }else{
            // return $masterResponse;
        // }

        if(count($masterResponse)){
            return response()->json([
                'status' => 200,
                'data' => $masterResponse,
                'message' => 'Records fetched successfully.',
            ]);
        }else{
            return response()->json([
                'status' => 500,
                'data' => [],
                'message' => 'No data found.',
            ]);
        }

        
    }

}
