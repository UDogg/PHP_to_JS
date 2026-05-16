<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class SanitizeExcelColumnRequest extends FormRequest
{
    public function authorize(): bool
    {
        return true;
    }

    public function rules(): array
    {
        return [
            'policystatus_column_master_id' => 'required|string|max:255',
            'sample_data' => 'nullable|string',
            'excel_column_name' => 'nullable|string',
            'lob_id' => 'required|integer',
            'sequence' => 'required|integer',
        ];
    }

}
