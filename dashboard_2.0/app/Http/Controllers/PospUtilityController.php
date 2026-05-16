<?php

namespace App\Http\Controllers;

use App\Exports\FailedRecordsExport;
use App\Imports\PospImport;
use App\Models\User;
use App\Services\ThirdPartyTokenService;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\Storage;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Validator;


class PospUtilityController extends Controller{
 
    protected $tokenService;

    public function __construct(ThirdPartyTokenService $tokenService)
    {
        $this->tokenService = $tokenService;
    }
    public function fetchData(Request $request){
     
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('motor-api');
  
        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;

        $methodType = 'GET';
        $body = [
            "masterType" => $request->masterType,
            "state_name" => $request->state_name,
            "state_id" => $request->state_id,
            "productSubTypeId" => $request->productSubTypeId,
            "manfId" => $request->manfId,
            "fuelType" => $request->fuelType,
            "modelId" => $request->modelId,
            "State" => $request->State,
        ];

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }

        return $data;

    }

    public function fetchSegement(Request $request)
    {
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];

        $apiUrl = config('motor-get-segment-api');
        $methodType = 'GET';
        $body = [
            "product_sub_type_id"=> $request->product_sub_type_id,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;

    }

    public function fetchIcBySegement(Request $request){

    $headers = [
        'accept' => 'application/json',
        'Content-Type' => 'application/json'
    ];
    $apiUrl = config('get-ic-by-segment'); 
    $methodType = 'GET';
    $body = [
        "product_sub_type_id"=> $request->product_sub_type_id==0 ? 'All' : $request->product_sub_type_id,
    ];

    $token = $this->tokenService->getToken($apiUrl);
    $headers['Validation'] = $token;

    $client = new Client();
    $jsonBody = json_encode($body);
    $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
    $response = $client->sendAsync($newRequest)->wait();
    $result = $response->getBody($apiUrl);
    $data = json_decode($result, true); 

    if(config('store_api_logs') == true){
        logApiRequestResponse(
            $apiUrl,
            $methodType,
            $body,
            $data,
            $response->getStatusCode(),
            $headers,
            $apiType = 'posp-utility'
        );
    }
    
    return $data;
    }

    public function getImdMapping(Request $request)
    {
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-imd-mapping');

        $methodType = 'POST';
        $body = [
            "product_sub_type_id" => $request->product_sub_type_id,
            "company_alias" => $request->company_alias,
            "seller_type" => $request->seller_type,
            "seller_user_id" => $request->seller_user_id
        ];
         
        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;
        

        $returnData = [];

        try {
  
            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'posp-utility'
                );
            }

            if($data['status'] == true){
                foreach ($data['data'] as $key => $value) {
                    $sellerUserId = $value['seller_user_id']; // Get seller_user_id from the object
                    if (isset($request->seller_user_id_and_name[$sellerUserId])) {
                        $data['data'][$key]['seller_user_name'] = $request->seller_user_id_and_name[$sellerUserId];
                    }
                }
            }

            if($data['status'] == true){
                foreach($data['data'] as $key => $value){

                    $returnData[] = [
                        "status" => true,
                        "pospName" => $value['seller_user_name'],
                        "pospCode" => $value['seller_user_id'],
                        "icValue" => $value['ic_integration_type'],
                        "imdId" => $value['imd_id'],
                        "imdCode" => $value['imd_code'],
                        "newbusiness" => [
                            "third_party" => in_array("third_party", $value['matrix']['newbusiness'] ?? []) ? true : false,
                            "comprehensive" => in_array("comprehensive", $value['matrix']['newbusiness'] ?? []) ? true : false,
                        ],
                        "renewal" => [
                            "own_damage" => in_array("own_damage", $value['matrix']['renewal'] ?? [] ) ? true : false,
                            "third_party" => in_array("third_party", $value['matrix']['renewal'] ?? []) ? true : false,
                            "comprehensive" => in_array("comprehensive", $value['matrix']['renewal'] ?? []) ? true : false,
                        ],
                        "rollover" => [
                            "own_damage" => in_array("own_damage", $value['matrix']['rollover'] ?? []) ? true : false,
                            "third_party" => in_array("third_party", $value['matrix']['rollover'] ?? []) ? true : false,
                            "comprehensive" => in_array("comprehensive", $value['matrix']['rollover'] ?? []) ? true : false,
                        ],
                        "breakin" => [
                            "own_damage" => in_array("own_damage", $value['matrix']['breakin'] ?? []) ? true : false,
                            "third_party" => in_array("third_party", $value['matrix']['breakin'] ?? []) ? true : false,
                            "comprehensive" => in_array("comprehensive", $value['matrix']['breakin'] ?? []) ? true : false,
                        ],
                    ];
                }

            }


            if ($data['status'] == false) {
                foreach ($request->seller_user_id_and_name as $key => $value) {
                    $returnData[] = [
                        "status" => false,
                        "pospName" => $value,
                        "pospCode" => $key,
                        "icValue" => $request->company_alias,
                        "imdId" => false,
                        "imdCode" => false,
                        "newbusiness" => [
                          "third_party" => true,   
                          "comprehensive" => true,
                        ],
                        "renewal" => [
                            "own_damage" => true,
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                        "rollover" => [
                            "own_damage" => true,
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                        "breakin" => [
                            "own_damage" => true,
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                    ];
                           
                      
                }
                return ($returnData);
            }

            $sellerUserIdsFromResponse = array_column($returnData, 'pospCode'); // Extract seller_user_id from response

            // Find missing seller_user_ids that are in request but not in response
            $missingSellerUserIds = array_diff($request->seller_user_id, $sellerUserIdsFromResponse);

            if (!empty($missingSellerUserIds)) {
                // These IDs were not found in the response
                foreach ($missingSellerUserIds as $missingId) {
                    $returnData[] = [
                        "status" => "first insert", // Mark as not found or first insert
                        "pospName" => $request->seller_user_id_and_name[$missingId] ?? "Unknown",
                        "pospCode" => $missingId,
                        "icValue" => $request->company_alias,
                        "imdId" => false,
                        "imdCode" => false,
                        "newbusiness" => [
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                        "renewal" => [
                            "own_damage" => true,
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                        "rollover" => [
                            "own_damage" => true,
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                        "breakin" => [
                            "own_damage" => true,
                            "third_party" => true,
                            "comprehensive" => true,
                        ],
                    ];
                }
            }

            return $returnData;
        
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
            foreach ($request->seller_user_id_and_name as $key => $value) {
                $returnData[] = [
                    "status" => "exception",
                    // "err-message" => $e->getMessage(),
                    "pospName" => $value,
                    "pospCode" => $key,
                    "icValue" => $request->company_alias,
                    "imdCode" => false,
                    "newbusiness" => [
                      "third_party" => true,   
                      "comprehensive" => true,
                    ],
                    "renewal" => [
                        "own_damage" => true,
                        "third_party" => true,
                        "comprehensive" => true,
                    ],
                    "rollover" => [
                        "own_damage" => true,
                        "third_party" => true,
                        "comprehensive" => true,
                    ],
                    "breakin" => [
                        "own_damage" => true,
                        "third_party" => true,
                        "comprehensive" => true,
                    ],
                ];
                       
                  
            }
            return ($returnData);
            
        }
    }

    public function getManfId(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-manf-id');  
    
        $methodType = 'GET';
        $body = [
            "masterType"=>"Manufacturer",
            "productSubTypeId" => $request->productSubTypeId,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }

        return $data;

    }

    public function getModelId(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-model-id');  
        $methodType = 'GET';
        $body = [
            "masterType"=>"Model",
            "productSubTypeId" => $request->productSubTypeId,
            "manfId" => $request->manfId,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;
    
        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }

        return $data;

    }

    public function getFueltype(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-fueltype');  
        $methodType = 'GET';
        $body = [
            "masterType"=>"Fuel",
            "productSubTypeId" => $request->productSubTypeId,
            "manfId" => $request->manfId,
            "modelId" => $request->modelId,
            // "modelId" => $request->modelId,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;
    
        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }

        return $data;

    }

    public function getVariant(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-Variant');  
        $methodType = 'GET';
        $body = [
            "masterType"=>"Variant",
            "productSubTypeId" => $request->productSubTypeId,
            "manfId" => $request->manfId,
            "modelId" => $request->modelId,
            "fuelType" => $request->fuelType,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;
    
        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }

        return $data;

    }

    public function getMmvMapping(Request $request)
    {

        $auth = Auth::user();
        $returnData = [];

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-mmv-mapping');

        $methodType = 'POST';
        $body = [
            "product_sub_type_id" => $request->product_sub_type_id==0 ? 'All' : $request->product_sub_type_id,
            "company_alias" => $request->company_alias,
            "seller_type" => strtoupper($request->seller_type),
            "seller_user_id" => $request->seller_user_id,
            "manfId" => $request->manfId ?? null,
            "modelId" => $request->modelId ?? null,
            "variant" => $request->variant ?? null,
            "fuelType" => $request->fuelType ?? null
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;

        try {

            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'posp-utility'
                );
            }

            $payload_seller_user_id = $request->seller_user_id ?? [];

            $responseApiData = collect($data['data'])
                ->unique('seller_user_id')
                ->pluck('seller_user_id')
                ->values()
                ->all() ?? 0;

            $missingSellerIds = array_diff($payload_seller_user_id, $responseApiData);

            $user_data = User::whereIn('id', $request->seller_user_id)
                ->get(['id', 'name', 'employee_code'])
                ->keyBy('id')
                ->toArray();

            $data['data'] = collect($data['data'])->map(function ($user) use ($user_data) {
                $seller = $user_data[$user['seller_user_id']] ?? null;

                $user['seller_user_name'] = $seller
                    ? (credential_decrypt($seller['name']) ?? '') . ' (' . ($seller['employee_code'] ?? '') . ')'
                    : '';

                return $user;
            })->toArray();

            // if (!empty($missingSellerIds)) {
            //     foreach ($missingSellerIds as $suid) {
            //         $returnData[] = [
            //             "status" => "Data not found",
            //             "seller_type" => $request->seller_type,
            //             "source" => "DASHBOARD",
            //             "product_sub_type_id" => $request->product_sub_type_id,
            //             "source_user_id" => $auth->id,
            //             "ic_integration_type" => $request->company_alias,
            //             "seller_user_id" => $suid,
            //             "matrix" => [
            //                 "allowed" => [
            //                     (object) [
            //                         "make" => $request->manfName ?? null,
            //                         "make_id" => $request->manfId ?? null,
            //                         "model_id" => $request->modelId ?? null,
            //                         "modelName" => $request->modelName ?? null,
            //                         "fuel" => $request->fuelType ?? null,
            //                         "variant_id" => $request->variant ?? null,
            //                     ]
            //                 ],
            //                 "denied" => []

            //             ]
            //         ];
            //     }
            // }

            array_push($data["data"], ...$returnData);
            return $data;
        } catch (\Exception $e) {

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }

            $returnData = [];

            // foreach ($request->seller_user_id as $suid) {
            //     $returnData[] = [
            //         "status" => "exception",
            //         "seller_type" => $request->seller_type,
            //         "source" => "DASHBOARD",
            //         "product_sub_type_id" => $request->product_sub_type_id,
            //         "source_user_id" => $auth->id,
            //         "ic_integration_type" => $request->company_alias,
            //         "seller_user_id" => $suid,
            //         "matrix" => [
            //             "allowed" => [
            //                 (object) [
            //                     "make" => $request->manfName ?? null,
            //                     "make_id" => $request->manfId ?? null,
            //                     "model_id" => $request->modelId ?? null,
            //                     "modelName" => $request->modelName ?? null,
            //                     "fuel" => $request->fuelType ?? null,
            //                     "variant_id" => $request->variant ?? null,
            //                 ]
            //             ],
            //             "denied" => []

            //         ]
            //     ];
            // }

            return response()->json([
                "status" => true,
                "message" => "No data found",
                "data" => $returnData
            ]);
        }
    }

    public function addMmvUtility(Request $request)
    {
        $auth = Auth::user();

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('add-mmv-utility');

        $methodType = 'POST';
        $body = [
            "seller_type" => strtoupper($request->seller_type),
            "source" => 'DASHBOARD',
            "segment_id" => $request->segment_id==0 ? 'All' : $request->segment_id,
            "source_user_id" => $auth->id,
            "ic_name" => $request->ic_name,
            "matrix" => $request->matrix
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;

        try {
          
            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'posp-utility'
                );
            }

            return $data;
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                    
                );
            }
        }
    }

    public function addRtoUtility(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('rto-utility');  

        $methodType = 'POST';

        $body = [
            "seller_type" => $request->seller_type,                 
            "source" => $request->source,                             
            "segment_id" => $request->segment_id,                  
            "source_user_id" => $request->source_user_id,           
            "ic_name" => $request->ic_name,                        
            "matrix" => $request->matrix
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;
        
        try{

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 
        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
        }
    }

    public function getRtoMapping(Request $request)
    {

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('get-rto-mapping');

        $methodType = 'POST';
        $body = [
            "product_sub_type_id" => $request->product_sub_type_id,
            "company_alias" => $request->company_alias,
            "seller_type" => $request->seller_type,
            "seller_user_id" => $request->seller_user_id,
            "state_id" => $request->state_id,
            "rto_id" => $request->rto_id,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;

        try {

            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            $filteredApiDuplicateData = collect($data['data'])
                ->unique('seller_user_id') // Keep only one entry per `seller_user_id`
                ->values() // Reset array keys
                ->all();

            $existingSellerIds = collect($filteredApiDuplicateData)->pluck('seller_user_id')->toArray();
            $missingSellerIds = array_diff($request['seller_user_id'], $existingSellerIds);

            $output = [];

            foreach($missingSellerIds as $missingSellerId){
                foreach($request->rto_id as $singleRto){
                    $output[] = [
                        "action" => false,
                        "icValue" => $request->company_alias,
                        "pospName" => $request->seller_user_id_and_name[$missingSellerId] ?? 'Unknown',
                        "pospCode" => $missingSellerId,
                        "stateId" => $request->state_id,
                        "rto_id" => $singleRto
                    ];
                }
                
            }

            $payloadRtoIds = $request->rto_id ?? [];
            $sellerUserIds = $request->seller_user_id ?? [];
            
            foreach ($sellerUserIds as $sellerId) {

                $sellerData = collect($filteredApiDuplicateData)->firstWhere('seller_user_id', $sellerId);

                if ($sellerData) {
                    $allowedRtoIds = collect($sellerData['matrix']['allowed'] ?? [])
                        ->pluck('rto_id')
                        ->flatten()
                        ->toArray();

                    $deniedRtoIds = collect($sellerData['matrix']['denied'] ?? [])
                        ->pluck('rto_id')
                        ->flatten()
                        ->toArray();

                    $existingRtoIds = array_merge($allowedRtoIds, $deniedRtoIds);

                    $missingRtos = array_diff($payloadRtoIds, $existingRtoIds);

                    foreach ($missingRtos as $mRto) {

                        $output[] = [
                            "action" => false,
                            "icValue" => $sellerData['ic_integration_type'],
                            "pospName" => $request->seller_user_id_and_name[$sellerId] ?? 'Unknown',
                            "pospCode" => $sellerId,
                            "stateId" => $sellerData['matrix']['allowed'][0]['state_id'] ?? 'Unknown',
                            "rto_id" => $mRto
                        ];
                    }
                }
            }

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'posp-utility'
                );
            }

            $payload = $request->all();

            foreach ($filteredApiDuplicateData as $item) {
                $icValue = $item['ic_integration_type'];
                $pospCode = $item['seller_user_id'];

                // seller_user_id_and_name se pospName map karo
                $pospName = $payload['seller_user_id_and_name'][$pospCode] ?? 'Unknown';

                foreach ($item['matrix']['denied'] as $denied) {
                    foreach ($denied['rto_id'] as $rto) {
                        if (in_array($rto, $payload['rto_id']) && $denied['state_id'] == $payload['state_id']) {
                            $output[] = [
                                "action" => false,
                                "icValue" => $icValue,
                                "pospName" => $pospName,
                                "pospCode" => $pospCode,
                                "stateId" => $denied['state_id'],
                                "rto_id" => $rto
                            ];
                        }
                    }
                }

                foreach ($item['matrix']['allowed'] as $allowed) {
                    foreach ($allowed['rto_id'] as $rto) {
                        if (in_array($rto, $payload['rto_id']) && $allowed['state_id'] == $payload['state_id']) {
                            $output[] = [
                                "action" => true,
                                "icValue" => $icValue,
                                "pospName" => $pospName,
                                "pospCode" => $pospCode,
                                "stateId" => $allowed['state_id'],
                                "rto_id" => $rto
                            ];
                        }
                    }
                }
            }

            return response()->json([
                "status" => true,
                "message" => "Filtered data found.",
                "data" => $output
            ]);
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }

            $returnData = [];
            foreach ($request->seller_user_id_and_name as $key => $value) {
                foreach ($request->rto_id as $rto) {

                    $returnData[] = [
                        "status" => "exception",
                        "action" => true,
                        "icValue" => $request->company_alias,
                        "pospName" => $value,
                        "pospCode" => $key,
                        "stateId" => $request->state_id,
                        "rto_id" => $rto,
                    ];
                }
            }

            return ($returnData);
        }
    }

    public function getRtoStates(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('rto_state_api');  

        $methodType = 'GET';
        $body = [
            "masterType" => "State",    
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;

        try{

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
        }
    }

    public function statewiseRto(Request $request){
       
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('rto_state_api');  

        $methodType = 'GET';
        $body = [
            "masterType" => "Rto",
            "state_id" => $request->state_id,
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;

        try{

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
        }
    }

    public function addIcParameter(Request $request){

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('add-ic-parameter-posp-utility');  
    
        $methodType = 'POST';
        $body = [
            "seller_type" => $request->seller_type,                
            "source" => $request->source,                            
            "segment_id" => $request->segment_id,                 
            "source_user_id" => $request->source_user_id,         
            "ic_integration_type" => $request->ic_integration_type, 
            "matrix" => $request->matrix
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;

        try {

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;

        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
        }
    }

    public function updateRecord(Request $request){
        $auth = Auth::user();
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('update-record-posp-utility');  

        $methodType = 'POST';
        $body = [
            "source" => $request->source,
            "segment_id" => $request->segment_id,
            "source_user_id" => $auth->id,
            "ic_integration_type" => $request->ic_name,
            "module_name" => 'MMV', 
            "operation" => $request->operation, 
            "seller_type" => $request->seller_type, 
            "seller_type_id" => $request->seller_user_id
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;
    
        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;

    }

    public function addImdCode(Request $request){
        
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('insert-imd-code');  

        $methodType = 'POST';
        $body = [
            "imd_code" => $request->imd_code,
            "segment_id" => $request->segment_id,     
            "ic_integration_type" => $request->ic_integration_type, 
            "source" => $request->source,                            
            "source_user_id" => $request->source_user_id, 
            "seller_type" => $request->seller_type,      
            "imd_fields" => $request->imd_fields
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json',
            'Origin' => request()->getHost(),
        ];
        $headers['Validation'] = $token;

        try {

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;

        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
        }
    }

    public function listImdCode(Request $request){
        
        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];
        $apiUrl = config('List-Imd-Code');  

        $methodType = 'POST';
        $body = [
            "segment_id" => $request->segment_id,     
            "ic_integration_type" => $request->ic_integration_type, 
            // "source" => $request->source,                            
            // "source_user_id" => $request->source_user_id, 
            "seller_type" => $request->seller_type,      
        ];

        $token = $this->tokenService->getToken($apiUrl);
        $headers['Validation'] = $token;

        try {

        $client = new Client();
        $jsonBody = json_encode($body);
        $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
        $response = $client->sendAsync($newRequest)->wait();
        $result = $response->getBody($apiUrl);
        $data = json_decode($result, true); 

        if(config('store_api_logs') == true){
            logApiRequestResponse(
                $apiUrl,
                $methodType,
                $body,
                $data,
                $response->getStatusCode(),
                $headers,
                $apiType = 'posp-utility'
            );
        }
        
        return $data;

        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'posp-utility'
                );
            }
        }
    }

    public function excelDownloadMmv(Request $request)
    {

        $excelFileName = 'mmv.xlsx';
        if(config('dashboard_storage_disk') === 's3'){
            $fileUrl = Storage::disk('s3')->temporaryUrl($excelFileName, now()->addMinutes(30));
        }else{
            $fileUrl = Storage::url($excelFileName);
        }
        // $this->ExcelLog($this->Auth->id, $excelFileName, 'UserExportTemplateDownload', 'completed', $request->all());

        return response()->json([
            'status' => 'success',
            'message' => 'File is ready for download.',
            'download_link' => $fileUrl,
        ]);

    }

    private function generateFailedRecordsExcel($FailedRecords)
    {
        $fileName = 'failed_records_' . now()->timestamp . '.xlsx';
        Excel::store(new FailedRecordsExport($FailedRecords), "public/{$fileName}");

        // Generate a URL for the file
        return asset("storage/{$fileName}");
    }

    public function pospUtilityImportExcel(Request $request){
        
        $validator = Validator::make($request->all(), [
            'file' => 'required|mimes:xlsx,csv',
        ]);
    
        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'errors' => $validator->errors()
            ], 422);
        }

        $import = new PospImport();
        Excel::import($import, $request->file('file'));
        $FailedRecords = $import->failedRecords;

        return response()->json([
            'status' => 'success',
            'message' => 'Excel data processed successfully!',
            'success_count' => $import->successCount,
            'failed_count' => $import->failedCount,
            'valid_records' => $import->validRecords,  
            'failed_records' => $import->failedRecords, 
            'Total_records' => $import->successCount + $import->failedCount,
            'failed_records_link' => $this->generateFailedRecordsExcel($FailedRecords) ?? null
        ]);

    


    }

    public function getUsersByUserType(Request $request){

        $allUsers = User::select('id','name','employee_code')->where('usertype',$request->usertype)->get();

        $output = [];

        foreach($allUsers as $user){
            $output[] = [
                'id' => $user->id,
                'name' => credential_decrypt($user->name),
                'employee_code' => $user->employee_code,
            ];
        }

        return response()->json([
            'status' => true,
            'data'=> $output,  
        ]);

    }


}


