<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Symfony\Component\HttpFoundation\Response;

class EncryptResponseMiddleware
{
    /**
     * Handle an incoming request.
     *
     * @param  \Closure(\Illuminate\Http\Request): (\Symfony\Component\HttpFoundation\Response)  $next
     */
    public function handle(Request $request, Closure $next): Response
    {
        /** @var Response $response */
        $response = $next($request);
        if ($request->header('X-Zeta-Flag') != 'true' || empty($response->getOriginalContent())) {
            return $response;
        }
        $originalData = $response->getOriginalContent();

        if (is_array($originalData) || is_object($originalData)) {

            if (
                (is_array($originalData) || is_object($originalData)) &&

                (is_array($originalData) ? array_key_exists('message', $originalData) : isset($originalData->message)) &&

                $originalData[ 'message' ] == 'You do not have permission to access this resource.'
            ) {
                $encrypted = getEncryptedPayload($originalData);

                return response()->json([
                    "response" => $encrypted,
                ], 403);
            }
            $encrypted = getEncryptedPayload($originalData);

            return response()->json([
                 "response" => $encrypted,
            ]);
        }

        return $response;
    }
}
