<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Spatie\Activitylog\LogOptions;
use Spatie\Activitylog\Traits\LogsActivity;
use Illuminate\Support\Facades\Request;
use Spatie\Activitylog\Models\Activity;

class BaseModel extends Model
{
    use HasFactory;
    use LogsActivity;

   
    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
        ->logAll();
    }
    public function tapActivity(Activity $activity, string $eventName)
    {
        $properties = $activity->properties->toArray();
        $properties['url'] = Request::fullUrl();
        $activity->properties = $properties;
    }
}
