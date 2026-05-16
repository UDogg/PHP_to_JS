<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SmsTemplate extends BaseModel
{
    use HasFactory;
    protected $table = 'sms_template';
    protected $primaryKey = 'template_id';
    protected $fillable = ['template_id','title','content','status'];
    protected $logAttributes = ['template_id','title','content','status'];
}
