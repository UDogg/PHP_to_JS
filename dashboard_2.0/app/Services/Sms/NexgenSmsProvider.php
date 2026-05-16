<?php
namespace App\Services\Sms;

use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;

class NexgenSmsProvider implements SmsProviderInterface
{
    public function sendSms(string $to, string $message, string $dlt_id)
    {
        // Build the URL and parameters for Nexgen API
        $url = config('SMSProviderUrl');
        // http://142.132.157.45/http-api.php?
        //username=enterusername&password=enterpassword&senderid=6char-senderid&route=1&number=enternumber&message=hellothere&templateid=XXXXXXX
        $rawmessage = rawurlencode($message);
        $finalmessage = str_replace(['%28', '%29'], ['(', ')'], $rawmessage);

        $params = [
            'username'      => config('SMSProviderUserid'),
            'password'    => config('SMSProviderPassword'),
            'senderid'         => 'WHIBPL',
            'route'    => 1,
            'number'     => $to,
            'message'         => $finalmessage,
            'templateid'           => $dlt_id,
        ];

        $queryString = collect($params)
        ->map(function ($value, $key) {
            return "{$key}={$value}";
        })
        ->implode('&');

        $fullUrl = $url . '?' . $queryString;

        try {
            $response = Http::get($fullUrl);
            if ($response->successful()) {
                Log::info("Nexgen SMS sent successfully to {$to}");
                return $response;
            } else {
                Log::error("Nexgen SMS failed: " . $response->body());
                return false;
            }
        } catch (\Exception $e) {
            Log::error("Nexgen SMS exception: " . $e->getMessage());
            return false;
        }
    }
}
