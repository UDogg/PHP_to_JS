<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class policyFilterMasterReq extends FormRequest
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
            'filter_name' => 'required|string|max:100',
            'filter_type' => 'required|string|max:100',
            // 'lob' => 'required|integer',
            // 'columns' => 'required|integer',
            // 'key' => 'required|string|max:100',
            // 'value' => 'required|string|max:100',
        ];
    }
}
