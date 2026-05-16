<?php
// app/Services/Sms/StatickingSmsProvider.php

namespace App\Services\Sms;

use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;

class StatickingSmsProvider implements SmsProviderInterface
{
    public function sendSms(string $to, string $message, string $dlt_id)
    {
        // Build the URL and parameters for Gupshup API
        $url = config('SMSProviderUrl');
        $params = [
            // 'method'      => 'SendMessage',
            'secret'    => config('SMSProviderPassword'),
            'sender'      => config('SMSProviderUserid'),
            'tempid'         => $dlt_id,
            'receiver'     => $to,
            'route'    => 'TA',
            'msgtype' => 1,
            'sms'         => $message,
        ];

        // Build the full URL with a properly encoded query string
        $fullUrl = $url . '?' . http_build_query($params);

        try {
            // Send the GET request to the SMS provider
            $response = Http::post($fullUrl);

            if ($response->successful()) {
                Log::info("Staticking SMS sent successfully to {$to}");
                return $response->body();
            } else {
                Log::error("Staticking SMS failed: " . $response->body());
                return false;
            }
        } catch (\Exception $e) {
            Log::error("Staticking SMS exception: " . $e->getMessage());
            return false;
        }
    }
}
