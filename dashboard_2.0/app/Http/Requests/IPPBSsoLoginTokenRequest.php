<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class IPPBSsoLoginTokenRequest extends FormRequest
{
    public function authorize()
    {
        return true;
    }

    public function rules()
    {
        return [
            'micrtoatm_session_id' => 'required|uuid',
            'request_data' => 'required|string'
        ];
    }

    public function messages()
    {
        return [
            'access_token.required' => 'Access token is required.',
            'request_data.required' => 'Encrypted request payload is required.'
        ];
    }
}
