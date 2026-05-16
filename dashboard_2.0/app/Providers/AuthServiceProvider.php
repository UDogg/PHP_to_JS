<?php

namespace App\Providers;

use Illuminate\Support\ServiceProvider;
use Laravel\Sanctum\PersonalAccessToken;
use Laravel\Sanctum\Sanctum;

class AuthServiceProvider extends ServiceProvider
{
    /**
     * Register services.
     */
    public function register(): void
    {
        //
    }

    /**
     * Bootstrap services.
     */
    public function boot(): void
    {
        $this->registerPolicies();

    // Customizing token validation to check for 'active' flag
    Sanctum::usePersonalAccessTokenModel(PersonalAccessToken::class);

    // Define a custom token validation callback
    Sanctum::authenticateAccessTokensUsing(function (PersonalAccessToken $token, $request) {
        return $token->active;  // Only allow active tokens
    });
    }
}
