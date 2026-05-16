<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class FormMaster extends BaseModel
{
    use HasFactory;

    protected $table = 'form_masters';
    protected  $fillable = ['label_name' , 'item_id', 'item_value' ];
    protected  $logAttributes = ['label_name' , 'item_id', 'item_value' ];

}
