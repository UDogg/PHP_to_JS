<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;
use Illuminate\Contracts\Validation\Validator;
use Illuminate\Http\Exceptions\HttpResponseException;

class PaymentGatewayRules extends FormRequest
{
    /**
     * Determine if the user is authorized to make this request.
     */
    public function authorize(): bool
    {
        return true;
    }

    /**
     * Prepare the data for validation.
     * Decrypt the encrypted payload.
     */
    protected function prepareForValidation(): void
    {
        $secretKey = config('FT_KEY');
        if (
            $this->isMethod('POST') &&
            $this->filled('request_data')
        ) {
            $encrypted = $this->input('request_data');
            
            $decrypted = ippb_decrypt_payload_sso($encrypted, $secretKey);
            if ($decrypted) {
                $decoded = json_decode($decrypted, true);
                
                if (is_array($decoded)) {
                    $this->merge($decoded);
                }
            }
        } else {
            if ($this->isMethod('POST') && !$this->filled('request_data')) {
                throw new HttpResponseException(
                    response()->json([
                        'app_response' => [
                            'timestamp' => now(),
                            'status'    => 'failure',
                            'message'   => 'Failed to update transaction',
                            'error_details' => [
                                'error_reason' => 'Error in update',
                                'request_data' => 'Request data is required for encrypted requests.'
                            ]
                        ]
                    ], 422)
                );
            }
        }
    }

    /**
     * Get the validation rules that apply to the request.
     *
     * @return array<string, \Illuminate\Contracts\Validation\ValidationRule|array<mixed>|string>
     */
    public function rules(): array
    {
        return [
            'customer_id' => 'required|string|max:100',
            'transaction_status' => 'required|string',
            'agent_id' => 'required|string|max:100',
            'session_id' => 'required|string|max:100',
        ];
    }
    public function messages()
    {
        return [
            'customer_id.required' => 'Customer ID is required.',
            'transaction_status.required' => 'Transaction Status is required.',
            'agent_id.required' => 'Agent ID is required.',
            'session_id.required' => 'Session ID is required.',
            'transaction_status.in' => 'Transaction Status must be either Success or Failed.',
        ];
    }

    protected function failedValidation(Validator $validator)
    {
        $errors = [];

        foreach ($validator->errors()->messages() as $field => $messages) {
            $errors[$field] = $messages[0];
        }

        $response_data = [
            'app_response' => [
                'timestamp' => now(),
                'status'    => 'failure',
                'message'   => 'Failed to update transaction',
                'error_details' => array_merge(
                    ['error_reason' => 'Error in update'],
                    $errors
                )
            ]
        ];

        $response_data = ippb_encrypt_payload_sso(json_encode($response_data), config('FT_KEY'));

        throw new HttpResponseException(
            response()->json(['response_data' =>$response_data],422)
        );
    }
}
