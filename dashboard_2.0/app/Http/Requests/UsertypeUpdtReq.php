<?php

namespace App\Http\Requests;

use Illuminate\Contracts\Validation\Validator;
use Illuminate\Foundation\Http\FormRequest;
use Illuminate\Http\Exceptions\HttpResponseException;

class UsertypeUpdtReq extends FormRequest
{
    /**
     * Determine if the user is authorized to make this request.
     */
    public function authorize(): bool
    {
        return true;
    }

    /**
     * Get the validation rules that apply to the request.
     *
     * @return array<string, \Illuminate\Contracts\Validation\ValidationRule|array<mixed>|string>
     */
    public function rules(): array
    {
        $rules = [
            'id' => 'required|integer',
            'UserType' => 'required',

        ];
        if($this->has('is_active'))
        {
            $rules['is_active'] = 'in:Y,N';
        }
        if($this->has('is_update'))
        {
            $rules['is_update'] = 'in:Y,N';
        }
        return $rules;

    }
    public  function failedValidation(Validator $validator)
    {
        $errors = $validator->errors();
        throw new HttpResponseException(response()->json([
            'status' => "false",
            'message' => 'Validation errors',
            'errors' => $errors
        ], 422));
    }
}
