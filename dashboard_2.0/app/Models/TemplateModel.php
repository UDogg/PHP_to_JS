<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Spatie\Activitylog\Traits\LogsActivity;
use Spatie\Activitylog\LogOptions;

class TemplateModel extends BaseModel
{
    // use LogsActivity;
    use HasFactory;
    protected $table = 'template_master';
    protected $primaryKey = 'template_id';
    protected $guarded = [];
    protected $fillable = [
        'title',
        'dlt_id',
        'alias',
        'content',
        'communication_type',
        'event',
        'status',
        'sent_at',
    ];

    protected $logAttributes = [
        'title',
        'dlt_id',
        'alias',
        'content',
        'communication_type',
        'event',
        'status',
        'sent_at',
    ];

    public function getStatusAttribute ($value) {
        return $value=='Y' ? 'Active' : 'Inactive';
    }
    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
    ->logAll()
    ->logOnlyDirty();
    }
}
