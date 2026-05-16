<?php

namespace App\Http\Middleware;

use Illuminate\Auth\Middleware\Authenticate as Middleware;
use Illuminate\Http\Request;

class Authenticate extends Middleware
{
    /**
     * Redirect the user to somewhere else when not authenticated.
     * For API, we return JSON instead of redirect.
     */
    protected function redirectTo(Request $request): ?string
    {
        // If request expects JSON, return nothing so no redirect happens
        if ($request->expectsJson()) {
            return null;
        }

        // If request is web but you dont want redirect, return null also
        return null;
    }

    /**
     * Handle unauthenticated user.
     */
    protected function unauthenticated($request, array $guards)
    {
        // Always return JSON for unauthorized request
        abort(response()->json([
            'status'  => false,
            'message' => 'You do not have permission to access to this resource.',
        ], 401));
    }
}
