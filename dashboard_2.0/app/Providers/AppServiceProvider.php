<?php

namespace App\Providers;

use Illuminate\Support\Facades\Gate;
use Illuminate\Support\ServiceProvider;
use Illuminate\Http\Request;

use App\Models\Credential;
use App\Services\MotorFetchService;
use App\Interfaces\PolicyStatusData;
use Illuminate\Support\Facades\Cache;
use Illuminate\Support\Facades\Schema;
use Illuminate\Support\Facades\Config;
use Illuminate\Support\Facades\Event;
use App\Events\EmailEvent;
use App\Listeners\SendEmail;
use App\Events\SmsEvent;
use App\Listeners\SendEmailQR;
use App\Listeners\SendSms;
use Illuminate\Support\Facades\URL;
use App\Events\SendOtpEvent;
use App\Listeners\SendOtpListener;
use Illuminate\Cache\RateLimiting\Limit;
use Illuminate\Support\Facades\RateLimiter;
use Laravel\Sanctum\Sanctum;
use App\Models\Customer;
use App\Models\User;

class AppServiceProvider extends ServiceProvider
{
    /**
     * Register any application services.
     */
    public function register(): void
    {
        $this->app->bind(PolicyStatusData::class,MotorFetchService::class);
    }

    /**
     * Bootstrap any application services.
     */
    public function boot(): void
    {
        if (!in_array(request()->getHost(), ['localhost', '127.0.0.1', '::1']) ) {
            URL::forceScheme('https');
        }
        RateLimiter::for('ApiRateLimiter', function (Request $request) {
            return Limit::perMinute(10)->by($request->ip());
        });
        Gate::before(function ($user, $ability) {
            return $user->hasRole('Super Admin') ? true : null;
        });
        // Sanctum::authenticateAccessTokensUsing(function ($accessToken, $isValid) {
        //     return Customer::find($accessToken->tokenable_id);
        // });
        Sanctum::authenticateAccessTokensUsing(function ($accessToken, $isValid) {
            $model = $accessToken->tokenable_type;
        
            if ($model === User::class) {
                return User::find($accessToken->tokenable_id);
            }
        
            if ($model === Customer::class) {
                return Customer::find($accessToken->tokenable_id);
            }
        
            return null;
        });
        Event::listen(
            EmailEvent::class,
            SendEmail::class,
            SmsEvent::class,
            SendSms::class,
            SendEmailQR::class,
            SendOtpEvent::class
        );
        self::setConfig();
    }
    static protected function setConfig()
    {

        $config = [];
        $has_table_config_settings = Cache::remember(request()->header('host') . '_has_table_config_settings', 3600, function () {
            return Schema::hasTable('config_settings');
        });


        if ($has_table_config_settings) {

            $configs = Cache::remember(request()->header('host') . '_config_settings', 3600, function () {
                return Credential::get(['credential_key', 'credential_value']);
            });

            foreach ($configs as $config) {
                Config::set(trim($config->credential_key), credential_decrypt(trim($config->credential_value)));
            }
        }

    }
}
