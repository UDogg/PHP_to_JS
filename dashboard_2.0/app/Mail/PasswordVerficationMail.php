<?php

namespace App\Mail;

use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Mail\Mailable;
use Illuminate\Mail\Mailables\Content;
use Illuminate\Mail\Mailables\Envelope;
use Illuminate\Queue\SerializesModels;

class PasswordVerficationMail extends Mailable
{
    use Queueable, SerializesModels;
    public $url;
    public $body;
    public $title;

    /**
     * Create a new message instance.
     */
    public function __construct($url, $body, $title)
    {
        $this->url = $url;
        $this->body = $body;
        $this->title = $title ?? 'Password Verification Mail';
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
            view: 'auth.forgetpasswordmail',
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
        $cc_mail = config('send-password-mail-cc');
        $plainText = $this->body;
        return $this->view('auth.forgetpasswordmail')->with(['contentData' => $plainText])->subject($this->title)
        ->when(!empty($cc_mail), function ($message) use ($cc_mail) {
            return $message->cc($cc_mail);
        });
    }
}
