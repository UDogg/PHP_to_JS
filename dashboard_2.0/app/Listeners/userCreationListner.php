<?php

namespace App\Listeners;

use App\Events\userCreation;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Support\Facades\Mail;
use App\Mail\GoogleAuthenticationEmail;
use App\Mail\UserCredentialEmail;

class userCreationListner
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
    public function handle(userCreation $event): void
    {
        Mail::to($event->new_email)->send(new UserCredentialEmail(
            $event->qrcode,
            $event->secret,

            $event->password,

            $event->body,
            $event->title,

            ''
        ));
    }
}
