<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
// use Illuminate\Database\Eloquent\Model;
// use Jenssegers\Mongodb\Eloquent\Model;
use MongoDB\Laravel\Eloquent\Model;

class MongoModel extends Model
{
    use HasFactory;
    protected $table = 'dashboard_transactions';
    protected $connection = 'mongodb';

}