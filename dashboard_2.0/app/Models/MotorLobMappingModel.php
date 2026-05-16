<?php

namespace App\Models;

use Spatie\Activitylog\LogOptions;
use Illuminate\Database\Eloquent\Model;
use Spatie\Activitylog\Traits\LogsActivity;
use Illuminate\Database\Eloquent\Factories\HasFactory;

class MotorLobMappingModel extends Model
{
    use HasFactory, LogsActivity;
    protected $table = 'motor_lob_mapping';
    protected $fillable = [
        'lob',
        'motor_lob',
        'report_ob',
        'is_active',
    ];

    protected  $logAttributes = [
        'lob',
        'motor_lob',
        'report_ob',
        'is_active',
    ];

    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
            ->logAll();
    }
}
