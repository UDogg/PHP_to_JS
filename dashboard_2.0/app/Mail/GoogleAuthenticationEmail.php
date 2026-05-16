<?php

namespace App\Mail;

use Illuminate\Bus\Queueable;
use Illuminate\Mail\Mailable;
use Illuminate\Queue\SerializesModels;

class GoogleAuthenticationEmail extends Mailable
{
    use Queueable, SerializesModels;

    public $qrCodeUrl;
    public $securityKey;
    public $password;
    public $body;
    public $title;
    public function __construct($qrCodeUrl, $securityKey,$password, $body, $title)
    {
        $this->qrCodeUrl = $qrCodeUrl;
        $this->securityKey = $securityKey;
        $this->password = $password;
        $this->body = $body;
        $this->title = $title ?? 'Password Verification Mail';
    }

    public function build()
    {
        $plainText = $this->body;
        return $this->view('auth.googleAuthMail')
        ->with([
            'contentData' => $plainText,
            'qrCodeUrl' => $this->qrCodeUrl,
            'secret' => $this->securityKey,
            'password' => $this->password
        ])->subject($this->title);

    }
}
