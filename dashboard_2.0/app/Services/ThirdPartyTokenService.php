<?php
namespace App\Services;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;

class ThirdPartyTokenService
{
    public function getToken($url): ?string
    {
        $tokenConfigCheck = config('ThirdPartyTokenGeneration', false);

        if ($tokenConfigCheck) {
            try {
                $response = Http::accept('application/json')
                    ->withBasicAuth(
                        config('ThirdPartyTokenGenerationMotorUserName'),
                        config('ThirdPartyTokenGenerationMotorPassword')
                    )
                    ->post(config('ThirdPartyTokenGenerationMotor'), [
                        'api_endpoint' => $url,
                    ]);

                if ($response->successful() && isset($response['token'])) {
                    return $response['token'];
                }

                return null;
            } catch (\Exception $e) {
                Log::error('Exception during token generation', [
                    'message' => $e->getMessage(),
                ]);
                return null; // Also needed here to fulfill return type
            }
        }

        return null; // <- This line fixes your error
    }
}
