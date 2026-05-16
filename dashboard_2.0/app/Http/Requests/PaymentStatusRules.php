<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;
use Illuminate\Contracts\Validation\Validator;
use Illuminate\Http\Exceptions\HttpResponseException;
class PaymentStatusRules extends FormRequest
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
            'agent_id' => 'required|integer',
            'customer_id' => 'required|string|max:100',
            'enquiry_id' => 'required|string|max:100',
            'product_code' => 'required|string|max:100',    
            'payable_amount' => 'required|integer',
        ];
    }
    public function messages()
    {
        return [
            'agent_id.required' => 'Agent ID is required.',
            'customer_id.required' => 'Customer ID is required.',
            'enquiry_id.required' => 'Enquiry ID is required.',
            'product_code.required' => 'Product Code is required.',
            'payable_amount.required' => 'Payable Amount is required.',
            ''
        ];
    }
    protected function failedValidation(Validator $validator)
    {
        $errors = [];

        foreach ($validator->errors()->messages() as $field => $messages) {
            $errors[$field] = $messages[0];
        }

        throw new HttpResponseException(
            response()->json([
                'app_response' => [
                    'timestamp' => now(),
                    'status'    => 'failure',
                    'message'   => 'Failed to update transaction',
                    'error_details' => array_merge(
                        ['error_reason' => 'Error in update'],
                        $errors
                    )
                ]
            ], 422)
        );
    }
}
