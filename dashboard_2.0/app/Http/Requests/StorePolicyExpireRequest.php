<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class StorePolicyExpireRequest extends FormRequest
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
            'user_id' => 'required|integer',
            'mobile_no' => 'nullable|integer',
            'policy_details' => 'required|array|min:1',
            'policy_details.*.lob_id' => 'required|integer',
            'policy_details.*.policy_no' => 'nullable|string',
            'policy_details.*.policy_end_date' => 'required|date',
        ];
    }
}
