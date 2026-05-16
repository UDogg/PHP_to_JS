<?php
// app/Services/Sms/GupshupSmsProvider.php

namespace App\Services\Sms;

use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;

class GupshupSmsProvider implements SmsProviderInterface
{
    public function sendSms(string $to, string $message, string $dlt_id)
    {
        // Build the URL and parameters for Gupshup API
        $url = config('SMSProviderUrl');
        // $url = 'https://enterprise.smsgupshup.com/GatewayAPI/rest';
        $params = [
            'method'      => 'SendMessage',
            'userid'      => config('SMSProviderUserid'),
            'password'    => config('SMSProviderPassword'),
            'udh'         => 0,
            'dlr-mask'    => 19,
            'auth_scheme' => 'plain',
            'send_to'     => $to,
            'v'           => '1.1',
            'msg'         => $message,
        ];

         // Optionally add headers (if needed)
        // $headers = [
        //     'Cookie' => env('GUPSHUP_COOKIE', ''),
        // ];

        try {
            $response = Http::get($url, $params);
            if ($response->successful()) {
                Log::info("Gupshup SMS sent successfully to {$to}");
                return $response->body();
            } else {
                Log::error("Gupshup SMS failed: " . $response->body());
                return false;
            }
        } catch (\Exception $e) {
            Log::error("Gupshup SMS exception: " . $e->getMessage());
            return false;
        }
    }
}
