<?php

namespace App\Listeners;

use App\Events\forgotpasswordEvent;
use App\Mail\PasswordVerficationMail;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Support\Facades\Mail;

class forgotpasswordListner
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
    public function handle(forgotpasswordEvent $event): void
    {
        Mail::to($event->email)->send(new PasswordVerficationMail($event->url, $event->body,$event->title));

    }
}
