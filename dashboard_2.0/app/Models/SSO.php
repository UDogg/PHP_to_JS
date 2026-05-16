<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class SSO extends Model
{
    use HasFactory;
    protected $table = "sso_api_tokens";
    protected $fillable = [
        "sso_api_token",
        "formData",
        "encrypted_form_data",
        "status"
    ];
}
