<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\SoftDeletes;
use Spatie\Activitylog\LogOptions;
use Spatie\Activitylog\Traits\LogsActivity;

class OfflineUploadPolicy extends Model
{
    use HasFactory, LogsActivity, SoftDeletes;

    protected $table = 'offline_upload_policy';

    protected $fillable = ['data'];

    protected $casts = [
        'data' => 'array',
    ];

    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
            ->logAll();
    }

    public function __get($key)
    {
        if (array_key_exists($key, $this->attributes)) {
            return parent::__get($key);
        }

        if (is_array($this->data) && array_key_exists($key, $this->data)) {
            return $this->data[$key];
        }

        return parent::__get($key);
    }
}
