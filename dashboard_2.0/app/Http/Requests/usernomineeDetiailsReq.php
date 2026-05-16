<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class usernomineeDetiailsReq extends FormRequest
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
            'id' => ['required','integer'],
            'nominee_name' => ['required','string'],
            'nominee_relation' => ['required','string'],
            'nominee_dob' => ['required','string'],
            'nominee_age' => ['required','string'],
            'nominee_email' => ['required','string'],
            'nominee_pincode' => ['required','string'],
            'nominee_mobile' => ['required','string'],


            //
        ];
    }
}
