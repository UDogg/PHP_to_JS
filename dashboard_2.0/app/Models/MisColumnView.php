<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class MisColumnView extends Model
{
    protected $table = "mis_column_views";

    protected $fillable = [
        'mongo_key',
        'existing_value',
        'new_value',
    ];
}
