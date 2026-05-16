<?php

namespace App\Http\Controllers;

use App\Models\lobMaster;
use App\Models\TokenModel;
use GuzzleHttp\Client;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Str;

class RenewalController extends Controller
{
    public function getRenewalLink(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'policy_no' => 'required',
            'vehicle_registration_number' => 'required',
            'lob' => 'required|string',
            'trace_id' => 'nullable',
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 422);
        }

        $user = Auth::user();
        $xutm = str::uuid();

        $user_type = DB::table('usertypes')
        ->where('id', $user->usertype)
        ->pluck('Identifier') 
        ->first();

        $lob_id = lobMaster::where('lob',$request->lob)->pluck('id')->first();
        $uppercaselobname = strtoupper($request->lob);

        if($uppercaselobname != 'CAR' && $uppercaselobname != 'BIKE'){
            $uppercaselobname = 'CV';
        }
 
        $insert = new TokenModel();
        $insert->seller_id = $user->id;
        $insert->seller_type = $user_type;
        $insert->xutm = $xutm;
        $insert->lob_id = $lob_id;
        $insert->save();

        if(config('renewal_direct_url')){
                    
            $apiUrl = config('Get_Renewal_Link_Url').strtolower($uppercaselobname).'/GenerateLead?is_renewal=Y&reg_no='.$request->vehicle_registration_number.'&policy_no='.$request->policy_no.'&xutm='.$xutm;
            
            $data = [
                'status'    => true,
                'redirection_url' => $apiUrl,
                'traceId' => null,
                'new_user_product_journey_id' => null
            ];
            return $data;
        }else{

            $headers = [
                'accept' => 'application/json',
                'Content-Type' => 'application/json',
                'Origin' => request()->headers->get('origin')
            ];
            $apiUrl = config('Get_Renewal_Link_Url');
            $methodType = 'POST';
            $body = [
                "reg_no" => $request->vehicle_registration_number,
                "policy_no" => $request->policy_no,
                "source" => "DEMO",
                "segment" =>  $uppercaselobname,
                "redirection" => "N",
                "xutm" => $xutm
            ];

            $client = new Client();
            $jsonBody = json_encode($body);
            try {

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
                        $headers
                    );
                }

                return $data;
            } catch (\Exception $e) {

                if (config('store_api_logs') == true) {
                    logApiRequestResponse(
                        $apiUrl,
                        $methodType,
                        $body,
                        $e->getMessage() ?? null,
                        $e->getCode() ?? null,
                        $headers
                    );
                }
                return response()->json([
                    'status' => false,
                    'message' => 'Error fetching data',
                    'error' => $e->getMessage(),
                ], 500);
            }
        }

    }
}
