<?php

namespace App\Mail;

use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Mail\Mailable;
use Illuminate\Mail\Mailables\Attachment;
use Illuminate\Mail\Mailables\Content;
use Illuminate\Mail\Mailables\Envelope;
use Illuminate\Queue\SerializesModels;

class UserExcelReady extends Mailable implements ShouldQueue
{
    use Queueable, SerializesModels;

    public $filePath;
    public $user;

    public function __construct( $filePath)
    {
        // $this->user = $user;
        $this->filePath = $filePath;
    }

    public function envelope(): Envelope
    {
        return new Envelope(
            subject: 'Your Excel Export is Ready',
        );
    }

    public function content(): Content
    {
        return new Content(
            markdown: 'emails.user.excel',
        );
    }

    public function attachments(): array
    {
        return [
            Attachment::fromPath(storage_path('app/public/' . $this->filePath))
                ->as('user_export.xlsx')
                ->withMime('application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')
        ];
    }
}



