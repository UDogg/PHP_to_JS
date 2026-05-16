<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class userTypes extends BaseModel
{
    use HasFactory;
    use SoftDeletes;
    protected  $table = 'usertypes';
    protected  $fillable = [
        'name',
        'Identifier',
        'is_active'

    ];
    protected  $logAttributes = [
        'name',
        'Identifier',
        'is_active'

    ];
}
