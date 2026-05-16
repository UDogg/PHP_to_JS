<?php

namespace App\Listeners;

use App\Events\requestQrEvent;
use App\Mail\GoogleAuthenticationEmail;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Support\Facades\Mail;

class requestQrListner
{
    /**
     * Create the event listener.
     */
    public function __construct()
    {

    }

    /**
     * Handle the event.
     */
    public function handle(requestQrEvent $event): void
    {
        // dd($event);
        Mail::to($event->email)->send(new GoogleAuthenticationEmail(
            $event->qrcode,
            $event->secret,

            $event->password,

            $event->body,
            $event->title,

            ''
        ));
    }
}
