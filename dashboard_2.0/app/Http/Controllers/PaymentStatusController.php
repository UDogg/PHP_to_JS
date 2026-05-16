<?php

namespace App\Http\Controllers;

use App\Http\Requests\PaymentGatewayRules;
use App\Models\LogsApi;
use App\Models\PaymentStatus;
use App\Models\TokenModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;

use App\Models\lobMaster;
use function Symfony\Component\Clock\now;

use App\Models\substagemaster;
use App\Models\StagemasterModel;
use App\Models\MongoModel;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\DB; 
class PaymentStatusController extends Controller
{
    public function paymentDetails(Request $request)
    {
        try {

            $journey = TokenModel::where('session_id', $request->session_id)
                ->where('decrypted_form_data->agent_id', $request->agent_id)
                ->where('decrypted_form_data->customer_id', $request->customer_id)
                ->where('decrypted_form_data->uuid', $request->uuid)
                ->first();

            if (! $journey) {
                return response()->json([
                    'app_response' => [
                        'status'  => 'error',
                        'message' => 'Journey details not matched',
                    ],
                ], 500);
            }

            $tokenData = null;

            if ($request->filled('xutm')) {
                $tokenData = TokenModel::where('xutm', $request->xutm)
                    ->select('session_id', 'decrypted_form_data')
                    ->first();
            }

            $newSessionId = $tokenData?->session_id ?? $request->session_id;

            $formData = is_array($tokenData?->decrypted_form_data)
                ? $tokenData->decrypted_form_data
                : json_decode($tokenData?->decrypted_form_data, true);

            $uuid = $formData['uuid'] ?? $request->uuid;

            $request->merge([
                'uuid' => $uuid,
                'session_id' => $newSessionId
            ]);

            $pgData = array_merge($request->all(), [
                'uuid' => $uuid,
            ]);

            $payment = PaymentStatus::updateOrCreate(
                [
                    'agent_id'    => $request->agent_id,
                    'customer_id' => $request->customer_id,
                    'session_id'  => $newSessionId,
                ],
                [
                    'enquiry_id'      => $request->enquiry_id,
                    'product_code'    => $request->product_code,
                    'payable_amount'  => $request->payable_amount,
                    'payment_status'  => 'payment_initiated',
                    'lob_id'          => $journey->lob_id ?? null,
                    'pg_additional_data' => json_encode([$pgData]),
                    'resumed_journey_session_id' =>  $newSessionId
                ]
            );

            logApiRequestResponse(
                'paymentDetails session records',
                'POST',
                'old session id '.$journey->session_id.' - '.$request->uuid,
                'new session id '.($tokenData?->session_id ?? 'NA').' - '.$uuid,
                200,
                $request->headers->all(),
                'paymentDetails'
            );

            if ($payment->payment_status == 'payment_initiated' || $payment->data_push == 'Y') {
                $payment->update(['data_push' => 'N']);
            }
            
            $pgResponse = $this->paymentGatewayRedirection($request);
            $redirectUrl = $pgResponse['appResponse']['RespDtls']['redirectURL'] ?? null;
            // $redirectUrl = 'https://103.108.118.97/MicroATM/resources/Appzillon?custId=89&sessionID=20251209145545578&langId=en&uuid=50000056261765272345578299516';
            $response = [
                'app_response' => [
                    'timestamp' => now()->format('Y-m-d H:i:s'),
                    'status' => 'success',
                    'message' => 'Transaction details created successfully.',
                    'redirect_url' => $redirectUrl,
                ],
            ];

            $lob = lobMaster::find($journey->lob_id);
            logApiRequestResponse(
                'paymentDetails'.'<br>'. 'LOB = '. $lob->lob .'<br>'. 'Trace ID = '.$payment->transaction_id,
                'POST',
                $request->all(),
                $response,
                200,
                $request->headers->all(),
                'paymentDetails'
            );

            return response()->json($response, 200);

        } catch (\Exception $e) {

            logApiRequestResponse(
                'paymentDetails',
                'POST',
                $request->all(),
                $e->getMessage(),
                500,
                $request->headers->all(),
                'paymentDetails'
            );

            return response()->json([
                'status' => 'error',
                'message' => 'Something went wrong',
            ], 500);
        }
    }

    public function PaymentAcknowledgement(PaymentGatewayRules $request)
    {
        
        $secretKey = config('FT_KEY');
        $response_data = ippb_encrypt_payload_sso('', $secretKey);
            logApiRequestResponse(
                'PaymentAcknowledgement - IPPB Callback Received - https://uatdashboardapi-ippb.fynity.in/api/PaymentAcknowledgement',
                'POST',
                $request->all(),
                '',
                200,
                $request->headers->all(),
                'PaymentAcknowledgement'
            );
        $payment = PaymentStatus::where('customer_id', $request->customer_id)
            ->where('session_id', $request->session_id)
            ->where('agent_id', $request->agent_id)
            ->first();
        if (! $payment) {
            $plainResponse = [
                'app_response' => [
                    'status' => 'failure',
                    'message' => 'No record found for this customer',
                ],
            ];
            $response_data = ippb_encrypt_payload_sso(json_encode($plainResponse), $secretKey);

            logApiRequestResponse(
                'PaymentAcknowledgement - No Record',
                'POST',
                $request->all(),
                json_encode($plainResponse),
                200,
                $request->headers->all(),
                'PaymentAcknowledgement'
            );

            return response()->json([
                'response_data' => $response_data,
            ]);
        }

        if ($payment->payment_status !== 'payment_initiated') {
            $plainResponse = [
                'app_response' => [
                    'status' => 'failure',
                    'message' => 'Payment is not in initiated state',
                ],
            ];
            $response_data = ippb_encrypt_payload_sso(json_encode($plainResponse), $secretKey);

            logApiRequestResponse(
                'PaymentAcknowledgement - Invalid State',
                'POST',
                $request->all(),
                json_encode($plainResponse),
                200,
                $request->headers->all(),
                'PaymentAcknowledgement'
            );

            return response()->json([
                'response_data' => $response_data,
            ]);
        }

        $payment->update([
            'payment_status' => 'payment_received',
            'transaction_id' => $request->transaction_id,
            'transaction_status' => Str::upper($request->transaction_status),
            'payment_failure_reason' => $request->payment_failure_reason,
            'call_back_additional_data' => json_encode([
                'other1' => $request->other1,
                'other2' => $request->other2,
                'other3' => $request->other3,
            ]),
        ]);


        $request->merge([
            'lob_id' => $payment->lob_id,
        ]);

        $updtaeRecord = $this->lobWiseData($request);


        if ($updtaeRecord instanceof \Illuminate\Http\JsonResponse
            && $updtaeRecord->getStatusCode() === 200) {

            PaymentStatus::where('session_id', $request->session_id)
                ->where('agent_id', $request->agent_id)
                ->where('customer_id', $request->customer_id)
                ->update([
                    'data_push' => 'Y',
                ]);

            return $this->paymentCommonResponce($payment->lob_id, $updtaeRecord);
        }
        $plainResponse = [
            'app_response' => [
                'timestamp' => now()->format('Y-m-d H:i:s'),
                    'status' => 'success',
                    'message' => 'Policy Created successfully.',
                    'return_url' => config('INDIA_POST_RETURN_URL'),
                    'policy_no' => $certificateData['certificate_no'] ?? null,
                    'policy_pdf' => $certificateData['certificate_download_url'] ?? []
                ],
            ];

            $response_data = ippb_encrypt_payload_sso(json_encode($plainResponse), $secretKey);
            logApiRequestResponse(
                'PaymentAcknowledgement - Final Success',
                'POST',
                $request->all(),
                json_encode($plainResponse),
                200,
                $request->headers->all(),
                'PaymentAcknowledgement'
            );

        return response()->json([
            'response_data' => $response_data,
        ]);
    }

    public function encryptPayload(Request $request)
    {
        $service = $request->input('service');

        if ($service == 'dashboard') {
            $secretkey = config('FT_KEY');
        } else {
            if ($request->secretkey) {
                $secretkey = $request->secretkey;
            } else {
                $secretkey = config('IPPB_KEY');
            }
        }
        $decryptData = $request->input('decrypted_data');

        if (empty($decryptData)) {
            return response()->json([
                'status' => false,
                'message' => 'decrypted_data is required',
            ], 422);
        }

        try {
            if (is_array($decryptData)) {
                $decryptData = json_encode($decryptData, JSON_UNESCAPED_SLASHES);
            }

            $encryptedData = ippb_encrypt_payload_sso($decryptData, $secretkey);

            if ($encryptedData === false) {
                return response()->json([
                    'status' => false,
                    'message' => 'Encryption failed',
                ], 500);
            }

            return response()->json([
                'status' => true,
                'encrypted_data' => $encryptedData,
            ], 200);

        } catch (\Throwable $e) {
            return response()->json([
                'status' => false,
                'message' => 'Encryption failed',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    public function decryptPayload(Request $request)
    {
        $service = $request->input('service');

        if ($service == 'dashboard') {
            $secretkey = config('FT_KEY');
        } else {
            if ($request->secretkey) {
                $secretkey = $request->secretkey;
            } else {
                $secretkey = config('IPPB_KEY');
            }
        }
        $encryptedData = $request->input('encrypted_data');

        if (empty($encryptedData)) {
            return response()->json([
                'status' => false,
                'message' => 'encrypted_data is required',
            ], 422);
        }

        try {
            $decrypted = ippb_decrypt_payload_sso($encryptedData, $secretkey);

            if ($decrypted === false) {
                return response()->json([
                    'status' => false,
                    'message' => 'Decryption failed',
                ], 500);
            }

            $decodedJson = json_decode($decrypted, true);

            return response()->json([
                // 'status'         => true,
                'decrypted_data' => json_last_error() === JSON_ERROR_NONE
                                    ? $decodedJson
                                    : $decrypted,
            ], 200);

        } catch (\Throwable $e) {
            return response()->json([
                'status' => false,
                'message' => 'Decryption failed',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    public function encryptPayloadIPPB(Request $request)
    {
        $decryptData = $request->input('decrypted_data');
        $service = $request->input('service');

        if ($service == 'dashboard') {
            $secretkey = config('FT_KEY');
        } else {
            $secretkey = config('IPPB_KEY');
        }

        if (empty($decryptData)) {
            return response()->json([
                'status' => false,
                'message' => 'decrypted_data is required',
            ], 422);
        }

        try {
            if (is_array($decryptData)) {
                $decryptData = json_encode($decryptData, JSON_UNESCAPED_SLASHES);
            }

            $encryptedData = encrypt_payload_ippb($decryptData, $secretkey);

            if ($encryptedData === false) {
                return response()->json([
                    'status' => false,
                    'message' => 'Encryption failed',
                ], 500);
            }

            return response()->json([
                'status' => true,
                'encrypted_data' => $encryptedData,
            ], 200);

        } catch (\Throwable $e) {
            return response()->json([
                'status' => false,
                'message' => 'Encryption failed',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    public function decryptPayloadIPPB(Request $request)
    {
        $encryptedData = $request->input('encrypted_data');

        if (empty($encryptedData)) {
            return response()->json([
                'status' => false,
                'message' => 'encrypted_data is required',
            ], 422);
        }

        try {
            $decrypted = decrypt_payload_ippb($encryptedData);

            if ($decrypted === false) {
                return response()->json([
                    'status' => false,
                    'message' => 'Decryption failed',
                ], 500);
            }

            $decodedJson = json_decode($decrypted, true);

            return response()->json([
                'decrypted_data' => json_last_error() === JSON_ERROR_NONE
                                    ? $decodedJson
                                    : $decrypted,
            ], 200);

        } catch (\Throwable $e) {
            return response()->json([
                'status' => false,
                'message' => 'Decryption failed',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    public function validateTokenIPPB(Request $request)
    {
        $token = $request->bearerToken();

        $tokenData = TokenModel::where('token', $token)
            ->select('decrypted_form_data', 'session_id', 'seller_id')
            ->first();

        if (! $tokenData) {
            return [];
        }

        $formData = json_decode($tokenData->decrypted_form_data, true);
        $payload = [
            'appBody' => [
                'FetchCustDtls' => [
                    'agentID' => $tokenData->seller_id,
                    'custId' => $formData['customer_id'],
                    'Token' => $tokenData->session_id,
                    'langId' => 'en',
                    'id' => $formData['uuid'],
                ],
                'ProductCode' => 'FYNTUNE',
                'SubProductCode' => '',
            ],
            'appHeader' => [
                'pwd' => '',
                'userID' => 'FYNTUNE',
                'channelID' => 'TAB',
            ],
        ];
        $ipbRandomNumber = 'IPB7a8d9ea0e4f94abd9b640f29ca599fe7';

        $encryptedPayload = encrypt_payload_ippb(json_encode($payload), $ipbRandomNumber);

        $encryptedRandomNumber = encrypt_payload_ippb($ipbRandomNumber);

        $finalRequest = [
            'req' => [
                'ProductName' => 'SBILIFE',
                'MetaData' => $encryptedPayload,
                'MetaInfo' => $encryptedRandomNumber,
            ],
        ];

        $url = 'https://103.108.118.20/IPPBMicroATMServerSIT/resources/ProdPayDtlsS2S';

        $response = Http::withoutVerifying()
            ->timeout(30)

            ->post($url, $finalRequest);

        $decryptedRes = decrypt_payload_ippb($response->json()['res']);
        $decryptedRes = json_decode($decryptedRes, true);

        logApiRequestResponse(
            $url,
            'POST',
            $finalRequest,
            $decryptedRes,
            500,
            $request->headers->all(),
            'Validate Token IPPB'
        );
        
        $responseSessionToken = $decryptedRes['appResponse']['sessionToken'] ?? null;

        if ((string) $responseSessionToken === (string) $tokenData->session_id) {
            $message = 'validation success';
        } else {
            $message = 'invalid session token';
        }

        return [
            'message' => $message,
            'session_id' => $tokenData->session_id,
            'ipb_random_number' => $ipbRandomNumber,
            'encrypted_payload' => $encryptedPayload,
            'response' => $response->json(),
        ];
    }

    public function paymentGatewayRedirection(Request $request)
    {
        $tokenData = TokenModel::where('session_id', $request->session_id)
            ->select('decrypted_form_data', 'session_id', 'seller_id', 'lob_id')
            ->first();
        if (! $tokenData) {
            return [];
        }
        $formData = json_decode($tokenData->decrypted_form_data, true);
        $payload = [
            'appHeader' => [
                'userID' => 'FYNTUNE',
                'pwd' => '',
                'channelID' => 'TAB',
            ],
            'appBody' => [
                'PreRedirectDtls' => [
                    'custId' => $request->customer_id,
                    'agentID' => $request->agent_id,
                    'session_id' => $request->session_id,
                    'uuid' => $formData['uuid'], // "50000068221767344277682665596",
                    'langId' => 'en',
                ],
                'ProdPaymentDtls' => [
                    'Merchant_Code' => $request->merchant_code,
                    'Merchant_Name' => $request->merchant_name,
                    'Merchant_ID' => '20231111111',
                    'Session_Token' => $request->session_id,
                    'TxnType' => 'NBPAY',
                    'Total_Debit_Amt' => (string) $request->total_amount,
                    'Policy_Name' => $request->policy_name,
                    'Policy_Holder_Name' => $formData['proposer_name'],
                    'Policy_Number' => (string) $request->policy_number,
                    'Payment_breakdown' => [
                        'Base_Amt' => (string) $request->base_amt,
                        'Base_Amt_Desc' => 'Premium Amount(excluding GST)',
                        'Charge_Amt_1' => '',
                        'Charge_TypeNarration_1' => '',
                        'Charge_Amt_2' => '',
                        'Charge_TypeNarration_2' => '',
                        'Tax_Amt_1' => (string) $request->tax_amt_1,
                        'Tax_Type_Narration_1' => 'GST',
                        'Tax_Amt_2' => '',
                        'Tax_Type_Narration_2' => '',
                        'Tax_Amt_3' => '',
                        'Tax_Type_Narration_3' => '',
                    ],
                    'Merchant_Ref_No' => $request->enquiry_id,
                    'Customer_ID' => $request->customer_id,
                    'IPPB_Customer' => 'Y',
                    'Channel_ID' => $request->customer_id,
                    'TimeStamp' => now()->format('Y-m-d H:i:s'),
                    'Auto_Debit_Reqd' => 'NO',
                    'Auto_Debit_Freq' => 'Single',
                    'Auto_Debit_Amt_Type' => 'Fixed',
                    'Auto_Debit_Fixed_Amt' => '',
                    'Auto_Debit_Min_Range_Amt' => '',
                    'Auto_Debit_Max_Range_Amt' => '',
                    'Auto_Debit_Account' => '',
                    'Auto_Debit_Start_Date' => '',
                    'Auto_Debit_End_Date' => '',
                    'Field2_Label' => 'Policy Number',
                    'Field2_Val' => (string) $request->policy_number,
                    'Field3_Label' => 'requestId',
                    'Field3_Val' => 'FYNTUNEReq_' . $request->enquiry_id,
                    'Field4_Label' => 'Address Details',
                    'Field4_Val' => $formData["address_of_proposer"],
                    'Field5_Label' => 'Mobile No',
                    'Field5_Val' => $formData['mobile_no'],
                    'Field6_Label' => 'Sum Assured',
                    'Field6_Val' => (string) $request->sum_insured,
                    'Field7_Label' => 'Policy Term',
                    'Field7_Val' => "1",
                    'Field1_Label' => 'Product Code',
                    'Field1_Val' => $request->product_code,
                    'Num_Custom_Fields' => '7',
                    'Doc1_Name' => '',
                    'Doc1_Path' => '',
                    'Doc2_Name' => '',
                    'Doc2_Path' => '',
                ],
            ],
        ];
        $ipbRandomNumber = generate_ippb_random_number();

        $encryptedPayload = ippb_encrypt_payload_sso(json_encode($payload), $ipbRandomNumber);
        $encryptedRandomNumber = ippb_encrypt_payload_sso($ipbRandomNumber);
        // dd($encryptedPayload,$ipbRandomNumber,$encryptedRandomNumber);

        $finalRequest = [
            'req' => [
                'ProductName' => 'FYNTUNE',
                'MetaData' => $encryptedPayload,
                'MetaInfo' => $encryptedRandomNumber,
            ],
        ];
        $url = config('INDIA_POST_PAYMENT_GATEWAY');

        $response = Http::withoutVerifying()
            ->timeout(30)

            ->post($url, $finalRequest);

        $decryptedRes = ippb_decrypt_payload_sso($response->json()['res']);
        $decryptedRes = json_decode($decryptedRes, true);
        // dd($decryptedRes);

        logApiRequestResponse(
            $url,
            'POST',
            $finalRequest,
            $decryptedRes,
            500,
            $request->headers->all(),
            'Payment Gateway Redirection'
        );

        return $decryptedRes;
    }

    public function lobWiseData(Request $request)
    {
        try {
            // $payment = PaymentStatus::where('data_push', 'N')
            // ->where(function ($query) use ($request) {
            //     $query->where('lob_id', $request->lob_id)
            //         ->orWhere(function ($q) use ($request) {
            //             $q->where('agent_id', $request->agent_id)
            //                 ->where('session_id', $request->session_id)
            //                 ->where('customer_id', $request->customer_id);
            //         });
            // })
            $payment = PaymentStatus::where('data_push', 'N')
                        ->where('lob_id', $request->lob_id)
                        ->where('agent_id', $request->agent_id)
                        ->where('session_id', $request->session_id)
                        ->where('customer_id', $request->customer_id)
            ->select('pg_additional_data', 'enquiry_id', 'agent_id', 'session_id','customer_id','product_code','payable_amount','transaction_id','transaction_status')
                ->first();
            
            if (! $payment) {
                return response()->json([
                    'app_response' => [
                        'timestamp' => now()->format('Y-m-d H:i:s'),
                        'status' => 'failure',
                        'message' => 'No record found for given LOB',
                    ],
                ], 404);
            }

            $pgData = json_decode($payment->pg_additional_data, true);

            $ackRequestPayload = array_merge([
                'enquiry_id'    => $payment->enquiry_id,
                'agent_id'      => $payment->agent_id,
                'customer_id'   => $payment->customer_id,
                'transaction_id'=> $payment->transaction_id,
                'transaction_status' => $payment->transaction_status,
                'status'        => $payment->transaction_status,
                'session_id'    => $payment->session_id,
                'product_code'  => $payment->product_code,
                'total_amount'  => $payment->payable_amount,
            ], $pgData[0]);

            $lobMaster = lobMaster::find($request->lob_id);
            if (!$lobMaster || !$lobMaster->lob) {
                return response()->json([
                    'app_response' => [
                        'timestamp' => now()->format('Y-m-d H:i:s'),
                        'status' => 'failure',
                        'message' => 'Invalid LOB ID or LOB name not found',
                    ],
                ], 400);
            }

            $configKey = 'IPPB_LOB_Payment_PUSH_' . str_replace(' ','_',$lobMaster->lob);
            $url = config($configKey);
            if (!$url) {
                return response()->json([
                    'app_response' => [
                        'timestamp' => now()->format('Y-m-d H:i:s'),
                        'status' => 'failure',
                        'message' => 'Invalid LOB ID',
                    ],
                ], 400);
            }

            $headers = [
                'Content-Type' => 'application/json',
                'Accept' => 'application/json',
            ];

            if (($lobMaster->lob == 'CAR' || $lobMaster->lob == 'BIKE')){
                $headers['Authorization'] = 'Bearer ' . base64_encode('REDIRECTIONPGURL');
            }
            if (($lobMaster->lob == 'Health')){
                $headers['trace_id'] = $payment->actual_trace_id;
            }

            $response = Http::withoutVerifying()
                ->timeout(60)
                ->withHeaders($headers)
                ->post($url, $ackRequestPayload);

            logApiRequestResponse(
                    'PaymentAcknowledgement - LOB Response.<br>' . $url .'<br>' . 'LOB = '.$lobMaster->lob .'<br>'. 'Trace ID = '.$payment->transaction_id,                  
                    'POST',
                    $ackRequestPayload,
                    $response->json(),
                    200,
                    '',
                    'PaymentAcknowledgement LOB Response'
                );
            PaymentStatus::where('lob_id', $request->lob_id)
                ->update(['data_push' => 'Y']);

            if ($response->successful()) {
                $responseBody = $response->json(); 

                return response()->json([
                    'app_response' => [
                        'timestamp' => now()->format('Y-m-d H:i:s'),
                        'status' => $response->successful() ? 'success' : 'failure',
                        'message' => $response->successful() 
                                        ? 'Data Pushed successfully'
                                        : 'LOB API failed',
                        'lob_api_response' => $responseBody, 
                        'response_details' => [
                            'other_1' => $pgData['other1'] ?? '',
                            'other_2' => $pgData['other2'] ?? '',
                            'other_3' => $pgData['other3'] ?? '',
                        ],
                    ],
                ], 200);
            }else{
                return response()->json([
                    'app_response' => [
                        'timestamp' => now()->format('Y-m-d H:i:s'),
                        'status' => 'success',
                        'message' => 'This may take a bit longer than usual—thanks for your patience',
                        'lob_api_response' => $response, 
                        'response_details' => [
                            'other_1' => $pgData['other1'] ?? '',
                            'other_2' => $pgData['other2'] ?? '',
                            'other_3' => $pgData['other3'] ?? '',
                        ],
                    ],
                ], 200);
            }

        } catch (\Exception $e) {
            return response()->json([
                'app_response' => [
                    'timestamp' => now()->format('Y-m-d H:i:s'),
                    'status' => 'failure',
                    'message' => 'Something went wrong',
                ],
            ], 500);
        }
    }

    private function paymentCommonResponce($lob_id, $response)
    {
        $secretKey = config('FT_KEY');

        $responseData = $response->getData(true);
        $certificateData = $responseData['app_response']['lob_api_response']['data'] ?? [];


        if($lob_id == 1 || $lob_id == 2){
            $certificateData = $responseData['app_response']['lob_api_response']?? [];
        }
        $appResponse = [
            'timestamp'  => now()->format('Y-m-d H:i:s'),
            'status'     => 'success',
            'message'    => 'Policy Created successfully.',
            'return_url' => config('INDIA_POST_RETURN_URL'),
        ];

        if ($lob_id == 13) {
            $appResponse['policy_no']  = $certificateData['certificate_no'] ?? null;
            $appResponse['policy_pdf'] = $certificateData['certificate_download_url'] ?? null;
            $appResponse['policy_status'] = 'Policy Issued';
        }

        if ($lob_id == 6) {
            $appResponse['policy_no']  = $certificateData['policy_no'] ?? null;
            $appResponse['policy_pdf'] = $certificateData['policy_pdf'] ?? null;
            $appResponse['policy_status'] = $certificateData['policy_status'] ?? null;
        }

        if ($lob_id == 1 || $lob_id == 2) {
            $appResponse['policy_no']  = $certificateData['policy_no'] ?? null;
            $appResponse['policy_pdf'] = $certificateData['policy_pdf'] ?? null;
            $appResponse['policy_status'] = $certificateData['policy_status'] ?? null;
        }

        $encryptedResponse = ippb_encrypt_payload_sso(json_encode([
            'app_response' => $appResponse,
        ]), $secretKey);

        return response()->json([
            'response_data' => $encryptedResponse,
        ]);
    }

    public function agentPolicyData(Request $request)
    {
        DB::connection('mongodb')->enableQueryLog();

        $user = Auth::user();
        $plainToken = (request()->bearerToken()) ?? request()->bearerToken();
        if (!$user) {
            return response()->json(['message' => 'Unauthorized'], 401);
        }
        

        $data = TokenModel::where('token', $plainToken)->first();
        $xutm = Str::uuid();
        TokenModel::where('token', $plainToken)->update(['xutm' => $xutm]);
        $user_id = (int) $user->id;
        $customer_id = $data->decrypted_form_data['customer_id'] ?? null;
        $today = \Carbon\Carbon::today()->format('Y-m-d');
        $startOfMonth = \Carbon\Carbon::now()->startOfMonth()->format('Y-m-d');

        $subStage = substagemaster::where('sub_stage_name', 'Policy Issued')
            ->pluck('sub_stage_name')
            ->first();

        $columns = [
                'trace_id',
                'proposer_name',
                'proposer_mobile',
                'proposer_emailid',
                'vehicle_registration_number',
                'company_name',
                'transaction_stage',
                'proposal_no',
                'policy_no',
                'proposal_url',
                'quote_url',
                'section',
                'policy_start_date',
                'policy_end_date',
                'lastupdated_time',
                'policy_doc_path',
                "seller_id"
            ];

        // $xutm = $data->xutm ?? '';
        // policies in current month till today
        $agentData =  MongoModel::where('seller_id', $user_id)->where('user_id', $customer_id)
            ->select($columns)
            ->whereIn('transaction_stage', [$subStage])
            ->whereBetween('lastupdated_time', [$startOfMonth, $today])
            ->get();

        
        

        // Recent Data
        $agentRecentData = MongoModel::where('seller_id', $user_id)->where('user_id', $customer_id)
            ->select($columns)
            ->whereNotIn('transaction_stage', [$subStage])
            ->when($request->section, fn($q) => $q->where('section', $request->section))
            ->orderBy('lastupdated_time', 'desc')
            ->get()
            ->map(function ($item) use ($xutm) {

                $updateUrl = function ($url) use ($xutm) {
                    if (!$url) return $url;
                    return str_contains($url,'xutm=')
                        ? preg_replace('/xutm=[^&]*/', 'xutm='.$xutm, $url)
                        : $url.(str_contains($url,'?') ? '&' : '?').'xutm='.$xutm;
                };

                $item->quote_url = $updateUrl($item->quote_url);
                $item->proposal_url = $updateUrl($item->proposal_url);
                
                if ($item->transaction_stage === "Quote - Buy Now") {
                    $item->resume_journey_url = ($item->quote_url);
                }elseif ($item->transaction_stage == 'Inspection Pending') {
                    if(config('Fetch_Inspection_status_by_API')){
                        $item->common_redirect_url = true;
                        $item->inspection_api = true;
                        $item->inspection_api = true;
                    }else{
                        $item->common_redirect_url = config('Inspection_check_api');
                        $item->resume_journey_url = config('Inspection_check_api');
                        $item->inspection_api = false;
                    }
                }else {
                    $item->resume_journey_url = ($item->proposal_url);
                }

                return $item;
            });

        return response()->json([
            'message' => 'Success',
            'mypoliciesData' => $agentData,
            'recentSummaryData' => $agentRecentData,
        ], 200);
    }
}