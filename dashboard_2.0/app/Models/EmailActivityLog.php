<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class EmailActivityLog extends Model
{
    use HasFactory;
    protected $table = 'email_activity_logs';
    protected $primaryKey = 'email_id';

    protected $fillable = [
        'email',
        'subject',
        'body',
        'type',
        'status',
        'sent_at',
    ];


}
