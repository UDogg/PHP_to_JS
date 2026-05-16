<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class UserBankDetailsReq extends FormRequest
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
           'bank_name' => ['required','string','max:100'],
            'bank_city' => ['required','string','max:100'],
            'account_no' => ['required','string','max:100'],
            'ifsc_code' => ['required','string','max:100'],
            'bank_branch' => ['required','string','max:100'],
            'account_holder_name' => ['required','string','max:100'],
            //
        ];
    }
}
