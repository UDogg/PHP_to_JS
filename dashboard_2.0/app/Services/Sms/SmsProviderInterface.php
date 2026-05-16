<?php
// app/Services/Sms/SmsProviderInterface.php

namespace App\Services\Sms;

interface SmsProviderInterface
{
    /**
     * Send an SMS message.
     *
     * @param string $to      The destination phone number.
     * @param string $message The message content.
     * @return mixed
     */
    public function sendSms(string $to, string $message, string $dlt_id);
}
