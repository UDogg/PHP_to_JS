<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;
use App\Rules\UniqueEncrypted;
use App\Rules\ExistsEncrypted;
use App\Rules\ExistsEncryptedRole;

class UserCreationRequest extends FormRequest
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
     * @return array<string, \Illuminate\Contracts\Validation\ValidationRule|array|string>
     */
    public function rules(): array
    {
        $rules = [];
        $users = $this->input('*'); // Capture all user entries

        foreach ($users as $index => $user) {
            $userType = $user['usertype'] ?? null;

            // Common validation rules
            $rules["$index.role"] = ['required','string', new ExistsEncryptedRole('name')];
            if ($userType != 'b2c') {
                // $rules["$index.reporting_role"] = ['required','string', new ExistsEncryptedRole('name')];
                $rules["$index.reporting_mobile_no"] = ['required', 'digits:10', new ExistsEncrypted('mobile')];
            }
            // User type-specific validation
            if ($userType === 'E') {
                $rules["$index.email"] = ['required', 'email', new UniqueEncrypted('email')];
                $rules["$index.mobile"] = ['required', 'digits:10', new UniqueEncrypted('mobile')];
                $rules["$index.employee_code"] = ['required', new UniqueEncrypted('employee_code')];
                $rules["$index.adhar_no"] = ['nullable', 'digits:12', new UniqueEncrypted('adhar_no')];
                $rules["$index.pan_no"] = ['nullable', 'regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/', new UniqueEncrypted('pan_no')];
            } elseif ($userType === 'P') {
                $rules["$index.email"] = ['required', 'email', new UniqueEncrypted('email')];
                $rules["$index.mobile"] = ['required', 'digits:10', new UniqueEncrypted('mobile')];
                $rules["$index.license_start_date"] = 'required|date';
                $rules["$index.license_end_date"] = 'required|date';
                $rules["$index.pos_code"] = ['required', new UniqueEncrypted('pos_code')];
                $rules["$index.adhar_no"] = ['required', 'digits:12', new UniqueEncrypted('adhar_no')];
                $rules["$index.pan_no"] = ['required', 'regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/', new UniqueEncrypted('pan_no')];
            } elseif (in_array($userType, ['Partner', 'b2c'])) {
                $rules["$index.email"] = ['required', 'email', new UniqueEncrypted('email')];
                $rules["$index.mobile"] = ['required', 'digits:10', new UniqueEncrypted('mobile')];
                $rules["$index.adhar_no"] = ['nullable', 'digits:12', new UniqueEncrypted('adhar_no')];
                $rules["$index.pan_no"] = ['nullable', 'regex:/[A-Z]{5}[0-9]{4}[A-Z]{1}/', new UniqueEncrypted('pan_no')];
            }
        }

        return $rules;
    }

    /**
     * Custom validation messages.
     *
     * @return array<string, string>
     */
    public function messages(): array
    {
        return [
            '*.reporting_mobile_no.unique' => 'The reporting mobile number does not exist in our records.',
            '*.email.unique' => 'This email address is already in use.',
            '*.mobile.unique' => 'This mobile number is already in use.',
            '*.employee_code.unique' => 'This employee code is already in use.',
            '*.pos_code.unique' => 'This POS code is already in use.',
            '*.adhar_no.unique' => 'This Aadhar number is already in use.',
            '*.pan_no.unique' => 'This Pancard number is already in use.',
            '*.pan_no.regex' => 'The Pancard number must be in the format ABCDE1234F.',
            '*.mobile.digits' => 'The mobile number must be exactly 10 digits.',
            '*.reporting_mobile_no.digits' => 'The reporting mobile number must be exactly 10 digits.',
            '*.license_start_date.required' => 'The license start date is required for user type P.',
            '*.license_end_date.required' => 'The license end date is required for user type P.',
        ];
    }
}
