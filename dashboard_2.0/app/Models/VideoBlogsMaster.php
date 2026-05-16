<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Spatie\Activitylog\Traits\LogsActivity;
use Illuminate\Foundation\Auth\User as Authenticatable;
use Spatie\Activitylog\LogOptions;


class VideoBlogsMaster extends Authenticatable
{
    use HasFactory, LogsActivity;

    protected $table = 'video_and_blogs_changes';
    protected  $fillable = [
        'user_type',
        'content_type',
        'title',
        'description',
        'image',
        'link',
        'status',
        'role_id',

    ];
    protected $logAttributes = [
        'user_type',
        'content_type',
        'title',
        'description',
        'image',
        'link',
        'pincode',
        'status',
        'role_id',
    ];

    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
        ->logAll();
    }
}
