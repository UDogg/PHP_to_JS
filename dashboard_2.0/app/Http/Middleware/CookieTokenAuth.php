<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Laravel\Sanctum\PersonalAccessToken;
use Symfony\Component\HttpFoundation\Response;

class CookieTokenAuth
{
    public function handle(Request $request, Closure $next): Response
    {
        // Check for token in cookie
        $token = $request->cookie('token');
        $token = preg_replace('/%/', '|', $token, 1);
 
        if ($token) {
            $accessToken = PersonalAccessToken::findToken($token);

            if ($accessToken && $accessToken->tokenable) {
                auth()->setUser($accessToken->tokenable);
            }
        }

        return $next($request);
    }
}
