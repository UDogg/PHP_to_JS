<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use App\Models\SSO; 
use Carbon\Carbon;

class ValidateToken
{
    public function handle(Request $request, Closure $next)
    {
        // Get the token from the request header
        $token = $request->header('Authorization');
        
        if (!$token) {
            return response()->json([
                'message' => 'Token is missing',
            ], 401);
        }
        $expiryMinutes = Config('generateTokenApiToken_expiry', 30);

        // Check if the token exists in the database and is active
        $ssoToken = SSO::where('sso_api_token', $token)
            ->where('status', 'Y')
            ->first();

        if (!$ssoToken) {
            return response()->json([
                'message' => 'Invalid or expired token',
            ], 401);
        }
        $createdAt = Carbon::parse($ssoToken->created_at);
        $expiresAt = $createdAt->addMinutes($expiryMinutes); 
        $currentTime = Carbon::now();

        if ($currentTime->greaterThan($expiresAt)) {
            return response()->json([
                'message' => 'Token has expired',
            ], 401);
        }
        // Mark the token as used (update status to 'N')
        $ssoToken->update(['status' => 'N']);

        // Token is valid, proceed to the next middleware/controller
        return $next($request);
    }
}