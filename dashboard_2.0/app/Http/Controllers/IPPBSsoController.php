<?php

namespace App\Http\Controllers;

use App\Models\Customer;
use App\Models\LogsApi;
use App\Models\masterCompany;
use App\Models\SSO;
use App\Models\TokenModel;
use App\Models\User;
use App\Services\IPPBSsoService;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Hash;
use App\Models\lobMaster;

use function GuzzleHttp\json_encode;

class IPPBSsoController extends Controller
{
    protected IPPBSsoService $service;

    public function __construct(IPPBSsoService $service)
    {
        $this->service = $service;
    }

    public function create(Request $request)
    {
        if (! $request->filled('request_data')) {
            $response = ippb_encrypted_error_response('request_data is missing');
            $response->setStatusCode(500);

            logApiRequestResponse(
                'loginTokenValidate',
                'POST',
                null,
                'request_data is missing',
                500,
                $request->headers->all(),
                'sso-login-token-validate'
            );

            return $response;
        }
        $secretKey = config('FT_KEY');
        $decryptedPayload = ippb_decrypt_payload_sso($request->request_data, $secretKey);
        if (is_string($decryptedPayload)) {
            $decryptedPayload = json_decode($decryptedPayload, true);
        }
        if (! is_array($decryptedPayload)) {
            $response = ippb_encrypted_error_response('Invalid decrypted payload');
            $response->setStatusCode(500);

            logApiRequestResponse(
                'loginTokenValidate',
                'POST',
                ippb_decrypt_payload_sso($request->request_data, $secretKey),
                ('Invalid decrypted payload'),
                500,
                $request->headers->all(),
                'sso-login-token-validate'
            );

            return $response;
        }
        $username = $decryptedPayload['username'];
        $password = $decryptedPayload['password'];

        if ($username == config('ippb.basic_auth_user') && $password == config('ippb.basic_auth_pass')) {

            $uuidToken = Str::uuid()->toString();

            SSO::create([
                'sso_api_token' => $uuidToken,
                'status' => 'Y',
            ]);

            logApiRequestResponse(
                'generate_login_token',
                'POST',
                $request->all(),
                [
                    'status' => 'success',
                    'message' => 'Token generated successfully.',
                    'token' => $uuidToken,
                ],
                201,
                $request->headers->all()
            );

            $response_data = [
                'app_response' => [
                    'timestamp' => now()->toDateTimeString(),
                    'status' => 'success',
                    'response_details' => [
                        'token' => $uuidToken,
                        'message' => 'Token generated successfully.',
                    ],
                ],
            ];

            $response_data = ippb_encrypt_payload_sso(json_encode($response_data), $secretKey);

            return response()->json(['response_data' => $response_data], 201);

        } else {
            logApiRequestResponse(
                'generate_login_token',
                'POST',
                $request->all(),
                [
                    'status' => 'error',
                    'message' => 'Invalid Username & Password',
                ],
                401,
                $request->headers->all()
            );
            $response_data = [
                'app_response' => [
                    'timestamp' => now()->toDateTimeString(),
                    'status' => 'error',
                    'response_details' => [
                        'message' => 'Invalid Username & Password',
                    ],
                ],
            ];

            $response_data = ippb_encrypt_payload_sso(json_encode($response_data), $secretKey);

            return response()->json(['response_data' => $response_data], 401);
        }

    }

    public function loginTokenValidate(Request $request)
    {
        try {
            Log::info('IPPBSso loginTokenValidate API Hit', [
                'micrtoatm_session_id' => $request->micrtoatm_session_id,
                'request_data' => $request->request_data,
            ]);

            $secretKey = config('FT_KEY');
            if (! $request->filled('micrtoatm_session_id')) {
                $response = ippb_encrypted_error_response('micrtoatm_session_id is missing');
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    'micrtoatm_session_id is missing',
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }
            if (! $request->filled('request_data')) {
                $response = ippb_encrypted_error_response('request_data is missing');
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    null,
                    'request_data is missing',
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }
            $decryptedPayload = ippb_decrypt_payload_sso($request->request_data, $secretKey);

            if (! $decryptedPayload) {
                $response = ippb_encrypted_error_response('Decryption failed');
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    ('Decryption failed'),
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }

            if (is_string($decryptedPayload)) {
                $decryptedPayload = json_decode($decryptedPayload, true);
            }
            if (! is_array($decryptedPayload)) {
                $response = ippb_encrypted_error_response('Invalid decrypted payload');
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    ('Invalid decrypted payload'),
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }

            $decryptedData = $decryptedPayload['decrypted_data']
                    ?? $decryptedPayload
                    ?? [];
            if (!empty($decryptedData['customer_id'])) {

            $customerId = $decryptedData['customer_id'];

            $customerExists = Customer::get()->contains(function ($customer) use ($customerId) {
                return credential_decrypt($customer->username) == $customerId;
            });

            if (!$customerExists) {
                Customer::create([
                    'username' => credential_encrypt($customerId), 
                    'mobile'   => !empty($decryptedData['mobile_no']) 
                            ? credential_encrypt($decryptedData['mobile_no']) 
                            : null,
                    'email'    => !empty($decryptedData['email_id']) 
                                    ? credential_encrypt($decryptedData['email_id']) 
                                    : null,
                    'password' => Hash::make('Customer@123'),                        
                ]);
            }
        }

            if (! is_array($decryptedData)) {
                $decryptedData = [];
            }

            if (! empty($decryptedData) && ! isset($decryptedData['journey_type'])) {

                $message = 'Missing required fields in request_data: journey_type';

                $response = ippb_encrypted_error_response($message);
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    $decryptedPayload,
                    $message,
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }

            $requiredFields = ['uuid', 'session_id', 'agent_id', 'journey_type'];
            $missingFields = [];

            foreach ($requiredFields as $field) {
                if (! array_key_exists($field, $decryptedData) ||
                    $decryptedData[$field] === '' ||
                    $decryptedData[$field] === null
                ) {
                    $missingFields[] = $field;
                }
            }

            if (! empty($missingFields)) {

                $message = 'Missing required fields in request_data: '.implode(', ', $missingFields);

                $response = ippb_encrypted_error_response($message);
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    $decryptedPayload,
                    $message,
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }
            if ($decryptedData['journey_type'] == 'sell_now') {
                $requiredFieldsForSellNow = ['customer_id', 'mobile_no'];
                $missingFieldsForSellNow = [];

                foreach ($requiredFieldsForSellNow as $field) {
                    if (! array_key_exists($field, $decryptedData) ||
                        $decryptedData[$field] === '' ||
                        $decryptedData[$field] === null
                    ) {
                        $missingFieldsForSellNow[] = $field;
                    }
                }

                if (! empty($missingFieldsForSellNow)) {

                    $message = 'Missing required fields for sell_now journey in request_data: '.implode(', ', $missingFieldsForSellNow);

                    $response = ippb_encrypted_error_response($message);
                    $response->setStatusCode(500);

                    logApiRequestResponse(
                        'loginTokenValidate',
                        'POST',
                        $decryptedPayload,
                        $message,
                        500,
                        $request->headers->all(),
                        'sso-login-token-validate'
                    );

                    return $response;
                }
            }
            $sellerId = User::where('employee_code', $decryptedPayload['agent_id'])->first();

            if (! $sellerId) {
                $response = ippb_encrypted_error_response('Agent Details not found');
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    ('token validation fail'),
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }else{
                $sellerId = $sellerId->id;
            }

            $sellerType = $decryptedPayload['user_type'] ?? 'E';

            $result = $this->service->processToken(
                $request->micrtoatm_session_id,
                $request->request_data
            );

            if ($result instanceof \Illuminate\Http\JsonResponse) {
                return $result;
            }

            TokenModel::updateOrCreate(
                [
                    'session_id' => $request->micrtoatm_session_id,
                ],
                [
                    'encrypted_form_data' => $request->request_data,
                    'decrypted_form_data' => json_encode($decryptedPayload),
                    'seller_id' => $sellerId,
                    'seller_type' => $sellerType,
                    'lob_id' => 0,
                ]
            );

            if ($decryptedData['journey_type'] == 'sell_now') {
                $indiaPostValidation = $this->validateTokenIndiaPostCustDetails($request);
            } else {
                $indiaPostValidation = $this->validateTokenIndiaPostAgentDetails($request);
            }
            $errorMessage = $indiaPostValidation['errDesc']
                ?? $indiaPostValidation['message']
                ?? 'token validation fail';

            if (
                empty($indiaPostValidation) ||
                ! isset($indiaPostValidation['status']) ||
                ! $indiaPostValidation['status']
            ) {
                $response = ippb_encrypted_error_response($errorMessage);
                $response->setStatusCode(500);

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    $errorMessage,
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }

            if ($result['status']) {
                $token = null;
                if (isset($result['return_url'])) {
                    parse_str(parse_url($result['return_url'], PHP_URL_QUERY), $params);
                    $token = $params['xutm'] ?? null;
                }

                TokenModel::where(
                    'session_id',
                    $request->micrtoatm_session_id
                )->update([
                    'token' => $token,
                ]);

                $response_data = [
                    'app_response' => [
                        'timestamp' => now()->toDateTimeString(),
                        'status' => 'success',
                        'response_details' => [
                            'redirection_url' => $result['return_url'],
                            'other_1' => '',
                            'other_2' => '',
                            'other_3' => '',
                        ],
                    ],
                ];

                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    $response_data,
                    200,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                $response_data = ippb_encrypt_payload_sso(json_encode($response_data), $secretKey);

                return response()->json(['response_data' => $response_data]);
            }

            if (! $result['status']) {

                if (isset($result['encrypted_error'])) {
                    return response()->json([
                        'response_data' => $result['encrypted_error'],
                    ]);
                }

                $response = ippb_encrypted_error_response($result['message']);
                $response->setStatusCode(500);
                logApiRequestResponse(
                    'loginTokenValidate',
                    'POST',
                    ippb_decrypt_payload_sso($request->request_data, $secretKey),
                    $result['message'],
                    500,
                    $request->headers->all(),
                    'sso-login-token-validate'
                );

                return $response;
            }

        } catch (\Throwable $e) {
            Log::error('IPPBSso loginTokenValidate Exception', [
                'error' => $e->getMessage(),
            ]);

            $response = ippb_encrypted_error_response('Invalid encrypted request data catch');
            $response->setStatusCode(500);

            logApiRequestResponse(
                'loginTokenValidate',
                'POST',
                ippb_decrypt_payload_sso($request->request_data, $secretKey),
                'Invalid encrypted request data catch',
                500,
                $request->headers->all(),
                'sso-login-token-validate'
            );

            return $response;
        }
    }

    public function validateTokenIPPB(Request $request)
    {
        try {
            $tokenData = TokenModel::where('xutm', $request->token)->first();

            if (! $tokenData) {

                logApiRequestResponse(
                    'validateTokenIPPB',
                    'POST',
                    $request->all(),
                    'Invalid Token',
                    401,
                    $request->headers->all(),
                    'validateTokenIPPB'
                );

                return response()->json([
                    'status' => 500,
                    'message' => 'Invalid Token',
                ], 200);
            }
            $formData = [];

            $allowedLobs = [13, 14, 15, 16, 21, 22];
            if (in_array($tokenData->lob_id, $allowedLobs) && is_null($tokenData->decrypted_form_data)) {
                $formData = [
                    'PAN' => '-',
                    'address_of_proposer' => 'GRAM KOHA , KOHA,SAGAR, NIRTALA, 470117, 470117',
                    'agent_id' => '1080905',
                    'agent_name' => 'Nisha',
                    'bank_account_number' => '048910001043',
                    'branch_id' => 'IPOS0000001',
                    'branch_name' => 'KRISHNAGIRI BRANCH',
                    'customer_id' => '5000006822',
                    'dob' => '21-04-1992',
                    'email_id' => 'nisha7086@gmail.com',
                    'gender' => 'Female',
                    'kyc_flag' => 'N',
                    'mobile_no' => '7406925796',
                    'nominee_address' => 'Khushi 2256, Flat 101, 6th cross, Kudllu, Hongasandra B.O-Bangalore HQ, BANG5, KA, IN, 560068',
                    'nominee_dob' => '04-02-1999',
                    'nominee_name' => 'Swati',
                    'nominee_relationship' => 'WIF',
                    'pincode' => '470117',
                    'proposer_name' => 'Nisha Kumar ',
                    'proposer_salutation' => 'Miss.',
                    'session_id' => '20260116113615004',
                    'user_type' => 'E',
                    'uuid' => '50000068221768543575004694190',
                    'journey_type' => 'sell_now',
                ];

                TokenModel::where('xutm', $tokenData->xutm)->update([
                    'decrypted_form_data' => json_encode($formData),
                ]);
            }

            if (now()->diffInMinutes($tokenData->created_at) > 30) {

                logApiRequestResponse(
                    'validateTokenIPPB',
                    'POST',
                    $request->all(),
                    'Token expired',
                    401,
                    $request->headers->all(),
                    'validateTokenIPPB'
                );

                return response()->json([
                    'status' => 'false',
                    'data' => ['decrypted_form_data' => null],
                    'message' => 'Token expired',
                ], 200);
            }

            $decryptedFormData = $tokenData->decrypted_form_data ?
            json_decode($tokenData->decrypted_form_data, true)
            : $formData;

            $decryptedFormData['session_id'] = $tokenData->session_id;
            $companyList = masterCompany::get();

            if ($tokenData->seller_type === 'U') {
                $user = Customer::select(
                    'id as seller_id',
                    'usertype as usertype_id',
                    'name as seller_name',
                    'username',
                    'email',
                    'mobile'
                )->find($tokenData->seller_id);
            } else {

                $user = User::query()
                    ->leftJoin('user_additional_data', 'user_additional_data.user_id', '=', 'users.id')
                    ->leftJoin('user_branch_relation', 'user_branch_relation.user_id', '=', 'users.id')
                    ->leftJoin('au_branch_dump', 'au_branch_dump.branchid', '=', 'user_branch_relation.branch_id')
                    ->leftJoin('posp_ic_mappings', 'posp_ic_mappings.user_id', '=', 'users.id')
                    ->join('journey_api_token', 'journey_api_token.seller_id', '=', 'users.id')
                    ->where('users.id', $tokenData->seller_id)
                    ->select([
                        'users.id as seller_id', 'users.pos_code', 'users.usertype as usertype_id',
                        'users.name as seller_name', 'users.username', 'users.email', 'users.mobile',
                        'users.adhar_no as aadhar_no', 'users.pan_no',
                        'users.bank_city as city', 'users.employee_code',
                        'users.bank_branch as branch_name',
                        'journey_api_token.seller_type', 'journey_api_token.created_at',
                        'user_additional_data.is_sp', 'user_additional_data.sp_name',
                        'user_additional_data.sp_code',
                        'au_branch_dump.branchcode as branch_code',
                        'posp_ic_mappings.*',
                    ])->first();
            }

            if (! $user) {

                logApiRequestResponse(
                    'validateTokenIPPB',
                    'POST',
                    $request->all(),
                    'No Data Found',
                    404,
                    $request->headers->all(),
                    'validateTokenIPPB'
                );

                return response()->json([
                    'status' => 'false',
                    'message' => 'No Data Found',
                ], 200);
            }

            $decryptUsername = credential_decrypt($user->username);

            $user->seller_type = $tokenData->seller_type;
            $user->usertype = $tokenData->seller_type;
            $user->seller_name = $user->seller_name
                ? credential_decrypt($user->seller_name)
                : $decryptUsername;

            $user->username = $decryptUsername;
            $user->user_name = $decryptUsername;
            $user->email = credential_decrypt($user->email);
            $user->mobile = credential_decrypt($user->mobile);

            $user->city = $user->city ? credential_decrypt($user->city) : null;
            $user->branch_name = $user->branch_name ? credential_decrypt($user->branch_name) : null;
            $user->aadhar_no = $user->aadhar_no ? credential_decrypt($user->aadhar_no) : null;
            $user->pan_no = $user->pan_no ? credential_decrypt($user->pan_no) : null;

            $user->unique_number = $user->pos_code ?? null;

            if (config('ANG.Validation') == 'true') {
                $user->business_type = $tokenData->business_type;
                $user->business_code = $tokenData->business_code;
            }

            foreach ($companyList as $c) {
                $short = $c->company_shortname;
                if (! empty($user->{$short})) {
                    $user->{"relation_{$short}"} = $user->{$short};
                }
            }

            if ($user->seller_type === 'P') {
                $user->h_seller_id = $user->seller_id;
                $user->h_seller_type = 'Partner';
                $user->h_seller_user_name = $decryptUsername;
            } else {
                $user->h_seller_id = null;
                $user->h_seller_type = null;
                $user->h_seller_user_name = null;
            }

            //Customer ID
            $customerId = $decryptedFormData['customer_id'] ?? null;
            $user->user_id = null;
            if (!empty($customerId)) {
                $user->user_id = Customer::where(
                    'username',
                    credential_encrypt($customerId)
                )->value('id');
            }

            $user->customer_details = $decryptedFormData;
            $response = [
                'status' => 'true',
                'data' => $user,
                'message' => 'Data retrieved successfully',
            ];

            $lob = lobMaster::find($tokenData->lob_id);
            logApiRequestResponse(
                'validateTokenIPPB'.'<br>'.'LOB = '.$lob->lob,
                'POST',
                $request->all(),
                $response,
                200,
                $request->headers->all(),
                'validateTokenIPPB'
            );

            return response()->json($response, 200);

        } catch (\Exception $e) {

            logApiRequestResponse(
                'validateTokenIPPB',
                'POST',
                $request->all(),
                $e->getMessage(),
                500,
                $request->headers->all(),
                'validateTokenIPPB'
            );

            return response()->json([
                'status' => 'false',
                'message' => 'Internal Server Error',
            ], 500);
        }
    }

    public function validateTokenIndiaPostCustDetails(Request $request)
    {
        $tokenData = TokenModel::where('session_id', $request->micrtoatm_session_id)
            ->select('decrypted_form_data', 'session_id', 'seller_id')
            ->first();

        if (! $tokenData) {

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Invalid token',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Invalid token',
            ];
        }
        $formData = json_decode($tokenData->decrypted_form_data, true) ?? [];

        $payload = [
            'appBody' => [
                'FetchCustDtls' => [
                    'agentID' => $formData['agent_id'],
                    'custId' => $formData['customer_id'],
                    'Token' => $request->micrtoatm_session_id,
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
        $ipbRandomNumber = generate_ippb_random_number();

        if (empty($ipbRandomNumber)) {

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Failed to generate random number',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Failed to generate random number',
            ];
        }
        $encryptedPayload = ippb_encrypt_payload_sso(
            json_encode($payload, JSON_UNESCAPED_SLASHES),
            $ipbRandomNumber
        );
        $encryptedRandomNumber = ippb_encrypt_payload_sso($ipbRandomNumber);

        $finalRequest = [
            'req' => [
                'ProductName' => 'FYNTUNE',
                'MetaData' => $encryptedPayload,
                'MetaInfo' => $encryptedRandomNumber,
            ],
        ];

        $url = config('INDIA_POST_CUSTOMER_VALIDATE_TOKEN');

        $response = Http::withoutVerifying()
            ->timeout(30)

            ->post($url, $finalRequest);
        if (! $response->ok() || empty($response->json()['res'])) {

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Invalid response from IPPB',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Invalid response from IPPB',
            ];
        }

        if (! isset($response->json()['res'])) {
            Log::error('IPPB response missing res', $response->json());

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Invalid IPPB response',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Invalid IPPB response',
            ];
        }
        $ippbStaticKey = config(
            'IPPB_KEY',
            'CHAN91D6CDA4042AFDD292EB03E84B2BALC'
        );

        $decryptedRes = ippb_decrypt_payload_sso(
            $response->json()['res'],
            $ippbStaticKey
        );

        $decryptedRes = json_decode($decryptedRes, true);

        LogsApi::insert([
            'request' => json_encode($payload),
            'response' => json_encode($decryptedRes),
            'method' => 'POST',
            'url' => $url,
            'created_at' => now(),
            'updated_at' => now(),
        ]);
        $appResponse = $decryptedRes['appResponse'] ?? [];

        $ippbStatus = $appResponse['status'] ?? 'failure';
        $errDesc = $appResponse['ErrDtls']['errDesc'] ?? null;
        $responseSessionToken = $appResponse['sessionToken'] ?? null;

        if ($ippbStatus !== 'success') {

            $finalError = $errDesc ?: 'token validation fail';
            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                $payload,
                $finalError,
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'errDesc' => $finalError,
                'message' => $finalError,
                'session_id' => $tokenData->session_id,
            ];
        }

        $isValid = ((string) $responseSessionToken === (string) $tokenData->session_id);

        return [
            'status' => $isValid,
            'message' => $isValid ? 'validation success' : 'token validation fail',
            'session_id' => $tokenData->session_id,
        ];
    }

    public function validateTokenIndiaPostAgentDetails(Request $request)
    {
        $tokenData = TokenModel::where('session_id', $request->micrtoatm_session_id)
            ->select('decrypted_form_data', 'session_id', 'seller_id')
            ->first();

        if (! $tokenData) {

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Invalid token',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Invalid token',
            ];
        }
        $formData = json_decode($tokenData->decrypted_form_data, true) ?? [];

        $payload = [
            'appBody' => [
                'FetchAgentDtls' => [
                    'agentID' => $formData['agent_id'],
                    'Token' => $request->micrtoatm_session_id,
                    'id' => $formData['uuid'],
                    'langId' => 'en',
                ],
                'ProductCode' => 'FYNTUNE',
            ],
            'appHeader' => [
                'pwd' => '',
                'userID' => 'FYNTUNE',
                'channelID' => 'TAB',
            ],
        ];
        $ipbRandomNumber = generate_ippb_random_number();

        if (empty($ipbRandomNumber)) {

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Failed to generate random number',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Failed to generate random number',
            ];
        }
        $encryptedPayload = ippb_encrypt_payload_sso(
            json_encode($payload, JSON_UNESCAPED_SLASHES),
            $ipbRandomNumber
        );
        $encryptedRandomNumber = ippb_encrypt_payload_sso($ipbRandomNumber);

        $finalRequest = [
            'req' => [
                'ProductName' => 'FYNTUNE',
                'MetaData' => $encryptedPayload,
                'MetaInfo' => $encryptedRandomNumber,
            ],
        ];

        $url = config('INDIA_POST_AGENT_VALIDATE_TOKEN');

        $response = Http::withoutVerifying()
            ->timeout(30)

            ->post($url, $finalRequest);
        if (! $response->ok() || empty($response->json()['res'])) {

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Invalid response from IPPB',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Invalid response from IPPB',
            ];
        }

        if (! isset($response->json()['res'])) {
            Log::error('IPPB response missing res', $response->json());

            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                ippb_decrypt_payload_sso($request),
                'Invalid IPPB response',
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'message' => 'Invalid IPPB response',
            ];
        }
        $ippbStaticKey = config(
            'IPPB_KEY',
            'CHAN91D6CDA4042AFDD292EB03E84B2BALC'
        );

        $decryptedRes = ippb_decrypt_payload_sso(
            $response->json()['res'],
            $ippbStaticKey
        );

        $decryptedRes = json_decode($decryptedRes, true);

        LogsApi::insert([
            'request' => json_encode($payload),
            'response' => json_encode($decryptedRes),
            'method' => 'POST',
            'url' => $url,
            'created_at' => now(),
            'updated_at' => now(),
        ]);
        $appResponse = $decryptedRes['appResponse'] ?? [];

        $ippbStatus = $appResponse['status'] ?? 'failure';
        $errDesc = $appResponse['ErrDtls']['errDesc'] ?? null;
        $responseSessionToken = $appResponse['sessionToken'] ?? null;

        if ($ippbStatus !== 'success') {

            $finalError = $errDesc ?: 'token validation fail';
            logApiRequestResponse(
                'validateTokenIndiaPost',
                'POST',
                $payload,
                $finalError,
                500,
                $request->headers->all(),
                'validateTokenIndiaPost'
            );

            return [
                'status' => false,
                'errDesc' => $finalError,
                'message' => $finalError,
                'session_id' => $tokenData->session_id,
            ];
        }

        $isValid = ((string) $responseSessionToken === (string) $tokenData->session_id);

        return [
            'status' => $isValid,
            'message' => $isValid ? 'validation success' : 'token validation fail',
            'session_id' => $tokenData->session_id,
        ];
    }

    public function redirectToIPPB(Request $request)
    {
        $tokenData = TokenModel::where('token', $request->bearerToken())->first();
        if ($tokenData) {
            $decryptedData = json_decode($tokenData['decrypted_form_data'], true);
            $custId = $decryptedData['customer_id'] ?? '';
            $sessionId = $decryptedData['session_id'] ?? '';
            $langId = 'en';
            $uuid = $decryptedData['uuid'] ?? '';

            if ($custId != '') {
                $url = 'https://103.108.118.97/MicroATM/resources/Appzillon?custId='.$custId.'&sessionID='.$sessionId.'&langId='.$langId.'&uuid='.$uuid.'&action=cancel';
            } else {
                $url = 'https://103.108.118.97/MicroATM/resources/Appzillon?custId=5000006822&sessionID=20260129102556113&langId=en&uuid=50000068221769662556113159318&action=cancel';
            }
        } else {
            $url = 'https://103.108.118.97/MicroATM/resources/Appzillon?custId=5000006822&sessionID=20260129102556113&langId=en&uuid=50000068221769662556113159318&action=cancel';
        }

        return [
            'redirect_url' => $url,
            'status' => 200,
        ];
    }
}
