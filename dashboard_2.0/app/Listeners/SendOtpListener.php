<?php

namespace App\Listeners;

use App\Events\SendOtpEvent;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Log;
use App\Models\SmsActivityLog;
use App\Services\Sms\SmsProviderInterface;


class SendOtpListener
{
    protected $smsProvider;

    public function __construct(SmsProviderInterface $smsProvider)
    {
        $this->smsProvider = $smsProvider;
    }
    public function handle(SendOtpEvent $event)
    {
        $user = $event->user;
        $otp = $event->otp;
        $template = $event->template;
        $dlt_id = $template->dlt_id;

        
         $message = str_replace('{{OTP}}', $otp, $template->content);
        
         $otpLog = SmsActivityLog::create([
            'user_id' => $user->id,
            'mobile' => credential_decrypt($user->mobile),
            'sent_at' => credential_decrypt($user->mobile),
            'message' => $message,
            'type' => 'Send OTP',
            // 'otp_expiry' => now()->addMinutes(10),
            'status' => 'pending',
        ]);
         
            // $url = 'https://enterprise.smsgupshup.com/GatewayAPI/rest';
            // $params = [
            //     'method' => 'SendMessage',
            //     'userid' => '2000246467',
            //     'password' => 'g8WjKzFp',
            //     'udh' => 0,
            //     'dlr-mask' => 19,
            //     'auth_scheme' => 'plain',
            //     'send_to' => credential_decrypt($user->mobile),
            //     'v' => '1.1',
            //     'msg' => $message,
            // ];
            
             //  $response = Http::get($url, $params);
             $response = $this->smsProvider->sendSms(credential_decrypt($user->mobile), $message,$dlt_id);

            //  dd($response);
             if ($response) {
                $otpLog->update([
                    'sent_at' => $response,
                    'status' => 'sent',
                ]);
                Log::info('SMS sent successfully to ' . credential_decrypt($user->mobile));
            } else {
                $otpLog->update([
                    'sent_at' => $response,
                    'status' => 'failed',
                ]);
                // Log::error('SMS failed: ' . $response->body());
            }
        
    }
}

