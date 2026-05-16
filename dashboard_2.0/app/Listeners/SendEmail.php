<?php

namespace App\Listeners;

use App\Events\EmailEvent;
use App\Mail\OTPVerificationMail;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Support\Facades\Mail;

class SendEmail
{
    /**
     * Create the event listener.
     */
    public function __construct()
    {
        //
    }

    /**
     * Handle the event.
     */
    public function handle(EmailEvent $event): void
    {


    }
}
