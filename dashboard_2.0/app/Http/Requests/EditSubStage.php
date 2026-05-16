<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class EditSubStage extends FormRequest
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
            //
            'mdl_sb_stg' => 'required|string|max:100',
            'mdl_stg_id' => 'required|integer',
            'mdl_sb_stg_old' => 'required|string|max:100',
        ];
    }
    public function messages()
        {
            return [
                'mdl_sb_stg.required' => 'Please Enter Sub Stage Name To Rename',
                'mdl_sb_stg.max' => 'Sub Stage Name should not exceed 100 characters',
                'mdl_stg_id.required' => 'Please Do not Modify Request',
                'mdl_stg_id.integer' => 'Please Do not Modify Request',
                'mdl_sb_stg_old.required' => 'Please Do not Modify Request',
                'mdl_sb_stg_old.string' => 'Please Do not Modify Request'

            ];
        }
}
