<?php

namespace App\Services;

use App\Models\SmsTemplate;
use App\Models\TemplateModel;
use Illuminate\Support\Facades\Http;

class SMSService
{
    protected $apiUrl;
    protected $userid;
    protected $password;
    protected $dltTemplateId;
    public function __construct()
    {
        $this->apiUrl = config('services.sms.api_url');
        $this->userid = config('services.sms.userid');
        $this->password = config('services.sms.password');
    }

    public function sendSms($to,$templateName,$smsData,$user)
    {
        $smsTempalteDetails = TemplateModel::select('dlt_id','title','event','content')->where('title', $templateName)->first();
        $content = $smsTempalteDetails->content;
        $varReplaveCOunt = substr_count($content, '{#var');
        for ($i = 0; $i < $varReplaveCOunt; $i++) {
            $content = str_replace('{#var'.$i.'#}', $smsData[$i], $content);
        }
        $response = Http::get($this->apiUrl, [
            'to'      => $to,
            'message' => $content,
            'method' => 'SendMessage',
            'msg_type' => 'TEXT',
            'userid' => $this->userid,
            'password' => $this->password,
            'auth_scheme' => 'plain',
            'v' => '1.1',
            'format' => 'text',
            'dltTemplateId' => $smsTempalteDetails->dlt_id,
        ]);

        if ($response->failed()) {
            $smsStatus = 'failed';
            SMSlogActivity($user,$content,$smsStatus);
            return $response->json();
        }
        else
        {
            $smsStatus = 'success';
            SMSlogActivity($user,$content,$smsStatus);
            return $response->successful();
        }
    }
}
