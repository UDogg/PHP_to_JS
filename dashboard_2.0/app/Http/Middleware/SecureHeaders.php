<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Symfony\Component\HttpFoundation\Response;

class SecureHeaders
{
    /**
     * Handle an incoming request.
     *
     * @param  \Closure(\Illuminate\Http\Request): (\Symfony\Component\HttpFoundation\Response)  $next
     */
    public function handle(Request $request, Closure $next): Response
    {
        $response = $next($request);

        // List of headers you want to remove
        $unwanted = [
            // 'X-Frame-Options',
            // 'X-Content-Type-Options',
            // 'X-XSS-Protection',
            // 'X-Ratelimit-Limit',
            // 'X-Ratelimit-Remaining',
            // 'X-Ratelimit-Reset',
            'X-Powered-By',
            'Server',
            'x-ratelimit-limit',
            'x-ratelimit-remaining'
        ];

        foreach ($unwanted as $header) {
            $response->headers->remove($header);
        }

        return $response;
    }
}
