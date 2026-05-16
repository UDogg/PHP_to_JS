<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class UpdtColumnMaster extends FormRequest
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
            'column_id' => 'required|integer',
            'column_name' => 'required',
            'alias' => 'required',
            //
        ];
    }
    public function messages()
    {
        return [
            'column_id.required' => 'A column id is required',
            'column_id.integer' => 'column id must be an integer',
            'column_name.required' => 'A column name is required',
            'alias.required' => 'An alias is required',
            //
        ];
    }
}
