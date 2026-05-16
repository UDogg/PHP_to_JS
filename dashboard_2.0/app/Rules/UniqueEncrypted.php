<?php

namespace App\Rules;

use Illuminate\Contracts\Validation\Rule;
use App\Models\User;
// use App\Helpers\EncryptionHelper; 

class UniqueEncrypted implements Rule
{
    protected $column;

    public function __construct($column)
    {
        $this->column = $column;
    }

    public function passes($attribute, $value)
    {
        $encryptedValue = credential_encrypt($value);
        return !User::where($this->column, $encryptedValue)->exists();
    }

    public function message()
    {
        return 'The :attribute has already been taken.';
    }
}