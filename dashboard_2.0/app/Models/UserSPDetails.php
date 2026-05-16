<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class UserSPDetails extends Model
{
    protected $table = 'user_sp_details';
    protected $fillable = [
        'user_id',
        'is_sp',
        'sp_code',
        'sp_type',
        'noc_issued',
        'sp_certificate_date',
        'certificate_valid_from',
        'certificate_valid_till',
    ];
}
