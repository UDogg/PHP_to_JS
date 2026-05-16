<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;

class BasicAuthMiddleware
{
    public function handle(Request $request, Closure $next)
    {
        $username = $request->getUser();
        $password = $request->getPassword();
        $secretKey = config('FT_KEY');
        $validUser = config('ippb.basic_auth_user','FyntuneUser');
        $validPass = config('ippb.basic_auth_pass','Fyntune@Pass2025');

        if ($username !== $validUser || $password !== $validPass) {
            if(config('basic_auth_validation')){
                return response()->json(["status" => 401,"timestamp" => now()->toDateTimeString(),
                "message" => "Unauthorized access"], 401)->header('WWW-Authenticate', 'Basic');    
            }

            $response_data = [
                "app_response" => [
                    "timestamp" => now()->toDateTimeString(),
                    "status" => "failure",
                    "error_details" => [
                        "error_reason" => "Unauthorized access",
                        "other_1" => "",
                        "other_2" => "",
                        "other_3" => ""
                    ]
                ]
            ];

            $response_data = ippb_encrypt_payload_sso(json_encode($response_data), $secretKey);

            return response()->json(['response_data' => $response_data], 401);
        }

        return $next($request);
    }
}
