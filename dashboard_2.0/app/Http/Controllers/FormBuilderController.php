<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\FormBuilderMaster;

class FormBuilderController extends Controller
{

    public function index()
    {
        return view('form_builder');
    }
    public function update(request $request)
    {
        $field_type = $request->field_type  ?? '';
        $placeholder_name = $request->placeholder ?? '';
        $is_required = $request->mandatory ?? '';
        $input_size = $request->size ?? '';

        $selectValues = isset($request->select_values) ? implode(',', $request->select_values) : null;
        $options_name = $selectValues ?? '';

        $label_name = $request->label_name ?? '';
        if (!empty($request)) {
            $data  = FormBuilderMaster::create([
                'field_type' => $field_type,
                'options_name' => $options_name,
                'placeholder_name' => $placeholder_name,
                'label_name' => $label_name,
                'is_required' => $is_required,
                'input_size' => $input_size

            ]);

            return ['status' => 200, 'success' => 'form Created Successfully'];
        } else {
            return ['status' => 503, 'error' => 'getting error'];
        }
    }
}
