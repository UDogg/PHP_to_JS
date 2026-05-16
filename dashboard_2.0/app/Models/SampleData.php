<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SampleData extends BaseModel
{
    use HasFactory;
    protected $table = 'sample_data';
    protected $primaryKey = 'sample_data_id';
    protected $fillable = [
        'lob_id',
        'lob',
        'value'
    ];
    protected $logAttributes = [
        'lob_id',
        'lob',
        'value'
    ];
}
