<?php

namespace App\Mail;

use Illuminate\Bus\Queueable;
use Illuminate\Mail\Mailable;
use Illuminate\Queue\SerializesModels;

class UserCredentialEmail extends Mailable
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
        $this->title = $title ?? 'User Credentials Mail';
    }

    public function build()
    {
        $cc_mail = config('send-password-mail-cc');
        $bcc_mail = config('send-password-mail-bcc');
        $plainText = $this->body;
        return $this->view('auth.userCredentialsMail')
        ->with([
            'contentData' => $plainText,
            'password' => $this->password
        ])->subject($this->title)
        ->when(!empty($cc_mail), function ($message) use ($cc_mail) {
            return $message->cc($cc_mail);
        })
        ->when(!empty($bcc_mail), function ($message) use ($bcc_mail) {
            return $message->bcc($bcc_mail);
        });
    }
}
