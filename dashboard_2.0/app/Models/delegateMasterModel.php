<?php

namespace App\Models;

use Spatie\Activitylog\LogOptions;
use Illuminate\Database\Eloquent\Model;
use Spatie\Activitylog\Traits\LogsActivity;
use Illuminate\Database\Eloquent\SoftDeletes;
use Illuminate\Database\Eloquent\Factories\HasFactory;

class delegateMasterModel extends Model
{
    use HasFactory, SoftDeletes, LogsActivity;
    protected $table = 'delegate_master';
    protected $fillable = [
        'user_id',
        'delegate_user_id',
        'is_active',
    ];
    protected $logAttributes = [
        'user_id',
        'delegate_user_id',
        'is_active',
        'created_at',
        'updated_at',
        'deleted_at',
    ];

    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
        ->logAll();
    }
}
