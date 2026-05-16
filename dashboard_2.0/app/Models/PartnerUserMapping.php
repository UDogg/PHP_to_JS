<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class PartnerUserMapping extends Model
{
    use HasFactory, SoftDeletes;
    protected $table = 'partner_user_mapping';
    protected $primaryKey = 'partner_id';

    protected $fillable = [
        'partner_name',
        'user_id',
        'theme_id',
        'logo',
        'favicon_icon',
        'status',
    ];
}
