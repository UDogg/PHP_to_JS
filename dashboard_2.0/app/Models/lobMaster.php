<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class lobMaster extends BaseModel
{
    use HasFactory;
    use SoftDeletes;
    protected $table = 'lob_master';
    protected $fillable = [
        'lob_name',
        'lob',
        'is_enabled',
        'frontend_url',
        'lob_icon',
        'lob_master_name',
        'payment_url',
        'customer_frontend_url'


    ];
    protected $logAttributes = [
        'lob_name',
        'lob',
        'is_enabled',
        'frontend_url',
        'lob_icon',
        'lob_master_name',
        'payment_url',
        'customer_frontend_url'


    ];
        public function users()
    {
        return $this->belongsToMany(User::class, 'user_lob_relation', 'id', 'id');
    }
}
