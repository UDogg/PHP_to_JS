<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use App\Models\SSO; 
use Carbon\Carbon;
use Illuminate\Support\Facades\Log; 

class ValidateTokenIPPB
{
    public function handle(Request $request, Closure $next)
    {
        // Get the token from the request header        
        $token = $request->bearerToken();

        if (!$token) {
            $response = ippb_encrypted_error_response('Unauthorized User');
            $response->setStatusCode(401);
            return $response;
        }
        $expiryMinutes = Config('generateTokenApiToken_expiry', 3000);

        // Check if the token exists in the database and is active
        $ssoToken = SSO::where('sso_api_token', $token)
            ->where('status', 'Y')
            ->first();

        if (!$ssoToken) {
            LogApiRequestResponse(
                'SSO Token Validation',
                'POST',
                $request->all(),
                [
                    'message' => 'Invalid or expired token',
                ],
                401,
                '',
                'Validate Token'
            );
            $response = ippb_encrypted_error_response('Invalid or expired token');
            $response->setStatusCode(401);
            return $response;
        }
        $createdAt = Carbon::parse($ssoToken->created_at);
        $expiresAt = $createdAt->addMinutes($expiryMinutes); 
        $currentTime = Carbon::now();

        if ($currentTime->greaterThan($expiresAt)) {
            $response = ippb_encrypted_error_response('Token has expired');
            $response->setStatusCode(401);
            return $response;
        }
        // Mark the token as used (update status to 'N')
        // $ssoToken->update(['status' => 'N']);

        // Token is valid, proceed to the next middleware/controller
        return $next($request);
    }
}
