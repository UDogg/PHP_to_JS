<?php

namespace App\Providers;

use Illuminate\Support\ServiceProvider;
use App\Services\Sms\SmsProviderInterface;
use App\Services\Sms\GupshupSmsProvider;
use App\Services\Sms\StatickingSmsProvider;
use App\Services\Sms\NexgenSmsProvider;
use Illuminate\Support\Facades\Schema;

class SmsServiceProvider extends ServiceProvider
{
    /**
     * Register services.
     */
    public function register(): void
    {
         
        if (Schema::hasTable('config_settings')) {
            $provider = \DB::table('config_settings')->where('credential_key', 'SMSProvider')->value('credential_value');

            switch (credential_decrypt($provider)) {
                case 'gupshup':
                    $this->app->bind(SmsProviderInterface::class, GupshupSmsProvider::class);
                    break;
                    
                case 'staticking':
                    $this->app->bind(SmsProviderInterface::class, StatickingSmsProvider::class);
                    break;

                case 'nextgen':
                        $this->app->bind(SmsProviderInterface::class, NexgenSmsProvider::class);
                        break;    
                    
                default:
                    $this->app->bind(SmsProviderInterface::class, GupshupSmsProvider::class);
                    break;
            }
        }
    }

    /**
     * Bootstrap services.
     */
    public function boot(): void
    {
        //
    }
}
