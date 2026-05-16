<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
// use Illuminate\Database\Eloquent\Model;
// use Jenssegers\Mongodb\Eloquent\Model;
use MongoDB\Laravel\Eloquent\Model;

class CancelLogsCollectionModel extends Model
{
    use HasFactory;
    protected $table = 'update_stage_logs_dashboard_action';
    protected $connection = 'mongodb';


}


