<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Symfony\Component\HttpFoundation\Response;

class EncryptDecryptPayloadMiddleware
{
    /**
     * Handle incoming request and outgoing response.
     */
    public function handle(Request $request, Closure $next): Response
    {
        // ➤ DECRYPT the request payload if necessary
        if (
            $request->header('X-Zeta-Flag') === 'true' &&
            $request->isMethod('POST') &&
            $request->has('data')
        ) {
            $decrypted = getDecryptedPayload($request->input('data'));

            if (!$decrypted) {
                return response()->json(['error' => 'Decryption failed.'], 400);
            }

            $request->merge(json_decode($decrypted, true));
        }

        // ➤ Sanitize input
        $sanitized = $this->clean($request->all());
        $request->merge($sanitized);

        // ➤ Continue the request lifecycle and get the response
        /** @var Response $response */
        $response = $next($request);

        // ➤ ENCRYPT the response payload if needed
        if (
            $request->header('X-Zeta-Flag') === 'true' &&
            $response->getOriginalContent()
        ) {
            $originalData = $response->getOriginalContent();

            if (is_array($originalData) || (is_object($originalData) && !empty((array) $originalData))) {
                $encrypted = getEncryptedPayload($originalData);

                return response()->json([
                    'response' => $encrypted,
                ]);
            }
        }

        return $response;
    }

    /**
     * Sanitize request input recursively
     */
    private function clean($input)
    {
        foreach ($input as $key => $value) {
            if (is_array($value)) {
                $input[$key] = $this->clean($value);
            } elseif (is_string($value)) {
                $input[$key] = strip_tags($value);
            }
        }
        return $input;
    }
}
