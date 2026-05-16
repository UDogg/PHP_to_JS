<?php

namespace App\Listeners;

use App\Events\EmailEvent;
use App\Mail\OTPVerificationMail;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Support\Facades\Mail;

class SendEmailQR
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
        Mail::to($event->to_email)->send(new OTPVerificationMail($event->otp, $event->expiry,$event->body,$event->title));

    }
}
