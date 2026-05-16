<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class OemMasterData extends Model
{
    use HasFactory;

    protected $table = 'oem_master_data';
    protected $primaryKey = 'oem_id';
    protected $fillable = [
        'oem_name'
    ];
}
