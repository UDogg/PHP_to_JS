<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class SubStageReq extends FormRequest
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
            'stage_mstr' => "requiredif:action,==,''|integer",
            'sub_stage_name' => 'requiredif:action,==,""|string|max:100',
            'action' => "in:new",
            'new_substage_val' => 'string'
        ];
    }
    public function messages()
        {
            return [
                'stage_mstr.required' => 'Please Select Stage',
                'stage_mstr.integer' => 'Please Select Valid Stage',
                'sub_stage_name.required' => 'Please Enter Sub Stage Name',
                'sub_stage_name.max' => 'Sub Stage Name should not exceed 100 characters'

            ];
        }
}
