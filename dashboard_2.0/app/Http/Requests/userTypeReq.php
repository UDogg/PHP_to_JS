<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;
use Illuminate\Contracts\Validation\Validator;
use Illuminate\Http\Exceptions\HttpResponseException;

class userTypeReq extends FormRequest
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
        return [
            'UserType' => 'required|string|unique:usertypes,name,"","",deleted_at,null|max:75',
            'Userident' => 'required|string|unique:usertypes,Identifier|max:10',
            //
        ];
    }
    protected function failedValidation(Validator $validator)
    {
        $errors = $validator->errors();
        throw new HttpResponseException(response()->json([
            'status' => "false",
            'message' => 'Validation errors',
            'errors' => $errors
        ], 422));
    }
}
