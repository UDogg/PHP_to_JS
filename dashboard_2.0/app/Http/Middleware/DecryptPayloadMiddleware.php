<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Symfony\Component\HttpFoundation\Response;

class DecryptPayloadMiddleware
{
    /**
     * Handle an incoming request.
     */
    public function handle(Request $request, Closure $next): Response
    {
        if (
            $request->header('X-Zeta-Flag') === 'true' &&
            $request->filled('data')
        ) {
            $encrypted = $request->input('data');

            $decrypted = getDecryptedPayload($encrypted);

            if (!$decrypted) {
                return response()->json(['error' => 'Decryption failed.'], 400);
            }

            $decoded = json_decode($decrypted, true);

            if (!is_array($decoded)) {
                return response()->json(['error' => 'Invalid decrypted JSON.'], 400);
            }

            $request->merge($decoded);
        }

        $request->merge($this->clean($request->all()));

        return $next($request);
    }

    /**
     * Recursively clean input data by stripping HTML tags.
     */
    private function clean(array $input): array
    {
        foreach ($input as $key => $value) {
            $input[$key] = is_array($value)
                ? $this->clean($value)
                : (is_string($value) ? strip_tags($value) : $value);
        }

        return $input;
    }
}
