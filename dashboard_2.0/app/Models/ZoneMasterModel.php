<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
class ZoneMasterModel extends BaseModel
{
    use HasFactory;
    protected  $table = 'zone_master';
    protected $fillable = ['office_zone', 'office_name', 'parent_office', 'office_pincode', 'contact_phone', 'contact_email', 'address'];
    protected $logAttributes = ['office_zone', 'office_name', 'parent_office', 'office_pincode', 'contact_phone', 'contact_email', 'address'];
    
}
