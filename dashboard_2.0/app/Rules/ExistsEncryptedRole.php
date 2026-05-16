<?php

namespace App\Rules;

use Illuminate\Contracts\Validation\Rule;
use App\Models\Role;
// use App\Helpers\EncryptionHelper; 

class ExistsEncryptedRole implements Rule
{
    protected $column;

    public function __construct($column,)
    {
        $this->column = $column;
    }

    public function passes($attribute, $value)
    {
        return Role::where($this->column, $value)->exists();
    }

    public function message()
    {
        return 'The :attribute does not exist in our records.';
    }
}