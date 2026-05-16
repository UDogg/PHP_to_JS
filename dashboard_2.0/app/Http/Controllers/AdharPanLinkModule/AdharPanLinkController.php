<?php

namespace App\Http\Controllers\AdharPanLinkModule;

use App\Http\Controllers\Controller;
use App\Models\User;
use App\Services\ThirdPartyTokenService;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Http;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Http\Request;

class AdharPanLinkController extends Controller
{
    protected $tokenService;
    public function __construct(ThirdPartyTokenService $tokenService)
    {
        $this->tokenService = $tokenService;
    }
    public function aadhaarSeedingCheck(Request $request)
    {
        $auth = Auth::user();
        $userType = getUserTypeIdentifier($auth->usertype);

        if ($userType == 'P') {
            $adharPanLinkStatus = User::where('id', $auth->id)->pluck('pan_link_status')->first();

            if ($adharPanLinkStatus == 1) {
                return response()->json([
                    'status' => true,
                    'message' => 'Aadhaar and Pan already linked',
                ]);
            } else {
                // Form fields to be sent as multipart/form-data
                $multipart = [
                    [
                        'name' => 'mobile',
                        'contents' => credential_decrypt($auth->mobile) ?? '',
                    ],
                    [
                        'name' => 'email',
                        'contents' => credential_decrypt($auth->email) ?? '',
                    ],
                    [
                        'name' => 'pan_no',
                        'contents' => credential_decrypt($auth->pan_no) ?? '',
                    ],
                ];

                $apiUrl = config('AdharPanLinkApi');

                $methodType = 'POST';
                $body = $multipart;

                $token = $this->tokenService->getToken($apiUrl);
                
                try {
                    
                    $response = Http::withHeaders([
                        'Accept' => 'application/json',
                        // 'Validation' => $token,  
                    ]) ->asMultipart()
                    ->post($apiUrl, $multipart);

                    $data = $response->json();

                    if (config('store_api_logs') == true) {
                        logApiRequestResponse(
                            $apiUrl,
                            $methodType,
                            $body,
                            $data,
                            $response->getStatusCode(),
                            $response->headers(),
                            $apiType = 'Adhar-Pan-Link'
                        );
                    }

                    if ($data['status'] === "true") {
                        User::where('id', $auth->id)->update(['pan_link_status' => 1]);
                    }

                    return response()->json($data);

                } catch (\Exception $e) {
                    if (config('store_api_logs') == true) {
                        logApiRequestResponse(
                            $apiUrl,
                            $methodType,
                            $body,
                            $e->getMessage(),
                            $e->getCode() ?? 500,
                            $response->headers(),
                            $apiType = 'Adhar-Pan-Link'

                        );
                    }

                    return response()->json([
                        'status' => false,
                        'message' => 'Something went wrong',
                    ]);
                }
            }
        } else {
            return response()->json([
                'status' => false,
                'message' => 'Only Valid for Posp User',
            ]);
        }
    }
}
