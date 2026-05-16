<?php

namespace App\Mail;

use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Mail\Mailable;
use Illuminate\Mail\Mailables\Content;
use Illuminate\Mail\Mailables\Envelope;
use Illuminate\Queue\SerializesModels;

class OTPVerificationMail extends Mailable
{
    use Queueable, SerializesModels;
    public $otp;
    public $expiry;
    public $body;
    public $title;

    /**
     * Create a new message instance.
     */
    public function __construct($otp, $expiry, $body,  $title)
    {
        $this->otp = $otp;
        $this->expiry = $expiry;
        $this->body = $body;
        $this->title = $title ?? 'O T P Verification Mail';
    }

    /**
     * Get the message envelope.
     */


    /**
     * Get the message content definition.
     */
    public function content(): Content
    {
        return new Content(
            view: 'auth.loginOtpMail',
        );
    }

    /**
     * Get the attachments for the message.
     *
     * @return array<int, \Illuminate\Mail\Mailables\Attachment>
     */
    public function attachments(): array
    {
        return [];
    }
    public function build()
    {
        $plainText = $this->body;
        return $this->view('auth.loginOtpMail')->with(['contentData' => $plainText])->subject($this->title);
    }
}
