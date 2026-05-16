<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;
use Symfony\Component\HttpFoundation\Response;

class ThirdPartyTokenGenerationMiddleware
{
    public function handle(Request $request, Closure $next): Response
    {
        $tokenConfigCheck = config('ThirdPartyTokenGeneration', false);

        if ($tokenConfigCheck) {
            try {
                $response = Http::accept('application/json')
                    ->withBasicAuth(config('ThirdPartyTokenGenerationMotorUserName'), config('ThirdPartyTokenGenerationMotorPassword'))
                    ->post(config('ThirdPartyTokenGenerationMotor'), [
                        'api_endpoint' => $request->url(),
                    ]);

                if ($response->successful()) {
                    $token = $response->json('token');

                    if ($token) {
                        $request->headers->set('validation', $token);
                    }
                } else {
                    Log::error('Token generation failed', [
                        'status' => $response->status(),
                        'body' => $response->body(),
                    ]);
                }

            } catch (\Exception $e) {
                Log::error('Exception during token generation', [
                    'message' => $e->getMessage(),
                ]);
            }
        }
        return $next($request);
    }
}
