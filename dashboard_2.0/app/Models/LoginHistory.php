<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class LoginHistory extends Model
{
    use HasFactory;
    protected $table = 'login_history';
    protected $primaryKey = 'login_history_id';
    protected $fillable = [
        'user_id',
        'ip',
        'browser'
    ];
    public function user()
    {
        return $this->belongsTo(User::class, 'user_id', 'id');
    }
}
