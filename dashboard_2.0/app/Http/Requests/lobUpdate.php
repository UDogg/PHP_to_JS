<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class lobUpdate extends FormRequest
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
            'action' => 'required|string|in:add,remove',
            'lobs' => 'required|integer',
            //
        ];
    }
    public function messages()
        {
            return [
                'action.required' => 'Action is required',
                'action.string' => 'Action must be a string',
                'action.in' => 'This action is not allowed',
                'lobs.required' => 'Lobs is required',
                'lobs.integer' => 'Lobs must be an integer',
            ];
        }
}
