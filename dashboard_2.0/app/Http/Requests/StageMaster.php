<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class StageMaster extends FormRequest
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
            'stage_name' => 'required|string|max:100',
            //

        ];
    }
    public function messages()
        {
            return [
                'stage_name.required' => 'Please enter a stage name.',
                'stage_name.max' => 'Stage name should not exceed 100 characters.',
            ];
        }
}
