<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class PiFieldsModel extends Model
{
    protected $table = 'pi_fields_master';
    protected $fillable = [
        'field_name',
        'status'
    ];
}
