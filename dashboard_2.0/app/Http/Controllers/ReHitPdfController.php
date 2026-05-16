<?php

namespace App\Http\Controllers;

use App\Services\ThirdPartyTokenService;
use Exception;
use GuzzleHttp\Client;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Log;
use GuzzleHttp\Psr7\Request as Ghttp;

class ReHitPdfController extends Controller
{
    protected $tokenService;

    public function __construct(ThirdPartyTokenService $tokenService)
    {
        $this->tokenService = $tokenService;
    }
    public function generateRehitPdf(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        Log::info('Incoming Rehit PDF request', $request->all());

        $trace_id = $request->trace_id;
        $section = trim(strtoupper($request->section));
        $proposal_id = $request->proposal_id;

    
        if (!$trace_id || !$section) {
            return response()->json(['error' => 'Missing required fields: trace_id and/or section'], 400);
        }

        $motorSections = ['CAR', 'BIKE', 'PCV', 'GCV'];
        $healthSections = ['HEALTH', 'Super Top Up'];

        if (in_array($section, $motorSections)) {
            $apiUrl = config('Re-hit_pdf.MOTOR');
            $apiType = 'generate_rehit_pdf_motor';
            $body = [
                'enquiryId' => $trace_id,
            ];
        } elseif (in_array($section, $healthSections)) {
            if (!$proposal_id) {
                return response()->json(['error' => 'Missing required field: proposal_id'], 400);
            }
            $apiUrl = config('Re-hit_pdf.HEALTH');
            $apiType = 'generate_rehit_pdf_health';
            $body = [
                'trace_id' => $trace_id,
                'proposal_id' => $proposal_id,
            ];
        } else {
            return response()->json(['error' => 'Invalid section'], 400);
        }

        if (!$apiUrl) {
            Log::error("Missing API URL for section: $section");
            return response()->json(['error' => 'Internal configuration error'], 500);
        }

        try {
            $headers = [
                'accept' => 'application/json',
                'Content-Type' => 'application/json',
            ];

            $token = $this->tokenService->getToken($apiUrl);
            $headers['Validation'] = $token;

            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp('POST', $apiUrl, $headers, $jsonBody);

            $response = $client->sendAsync($newRequest)->wait();
            $statusCode = $response->getStatusCode();
            $result = $response->getBody()->getContents();
            $data = json_decode($result, true);

            $isstatus = false;
            if (isset($data['status'])) {
                $isstatus = $data['status'] === true || $data['status'] === 'true';
            }

            $data['status'] = $isstatus;

            Log::info("Rehit PDF API [$apiType] Response", [
                'status' => $statusCode,
                'data' => $data,
            ]);

            if (config('store_api_logs')) {
                logApiRequestResponse(
                    $apiUrl,
                    'POST',
                    $body,
                    $data,
                    $statusCode,
                    $headers,
                    $apiType
                );
            }

            return response()->json($data, $statusCode);
        } catch (Exception $e) {
            Log::error('Rehit PDF API call failed', [
                'message' => $e->getMessage(),
                'trace' => $e->getTraceAsString(),
            ]);

            if (config('store_api_logs')) {
                logApiRequestResponse(
                    $apiUrl,
                    'POST',
                    $body,
                    $e->getMessage(),     
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType
                );
            }

            return response()->json([
                'error' => 'API request failed',
                'message' => $e->getMessage(),
                'status' => false,
            ], 500);
        }

    }  

}
