<?php

namespace App\Listeners;

use App\Events\resendOtpEvent;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Queue\InteractsWithQueue;

class resendOtpListner
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
    public function handle(resendOtpEvent $event): void
    {
        //
    }
}
