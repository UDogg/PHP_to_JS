<?php

namespace App\Mail;

use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Mail\Mailable;
use Illuminate\Mail\Mailables\Content;
use Illuminate\Mail\Mailables\Envelope;
use Illuminate\Queue\SerializesModels;

class RaiseQueryMail extends Mailable
{
    use Queueable, SerializesModels;

    public string $subjectLine;
    public string $htmlBody;

    /**
     * Create a new message instance.
     */
    public function __construct(string $subjectLine, string $htmlBody)
    {
        $this->subjectLine = $subjectLine;
        $this->htmlBody = $htmlBody;
    }

    /**
     * Get the message envelope.
     */

    public function build()
    {
        return $this->subject($this->subjectLine)
            ->view('emails.generic_template')
            ->with([
                'htmlBody' => $this->htmlBody,
            ]);
    }
   
}
