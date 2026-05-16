<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class CorporateDomainMapping extends Model
{
    use HasFactory;
    protected $table = "corporate_domain_mapping";

    protected $fillable = [
        'id',
        'domain_name',
        'corporate_id',
        'status',
        'is_verified',
    ];
}
