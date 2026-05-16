<?php
namespace App\Mail;

use App\Models\DataExportLog;
use Illuminate\Bus\Queueable;
use Illuminate\Mail\Mailable;
use Illuminate\Queue\SerializesModels;
use Illuminate\Contracts\Queue\ShouldQueue;

class ExcelBatchMail extends Mailable
{
    use Queueable, SerializesModels;

    /**
     * Create a new message instance.
     *
     * @return void
     */
    protected $url , $uid;
    public function __construct($url , $uid)
    {
        $this->url = $url;
        $this->uid = $uid;
    }

    /**
     * Build the message.
     *
     * @return $this
     */
    public function build()
    {
        $url = asset('storage/' . $this->url);
        $data = DataExportLog::where('uid', $this->uid)->update(['status' => 'completed']);
        return $this->subject('PolicyStatusExport logs')->view('emails.excel_batch',['url'=> $this->url]); 
    }
}
