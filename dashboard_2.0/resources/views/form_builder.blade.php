@extends('layout.app', ['title' => 'form_builder'])
<!-- Main content -->
@section('content')
<!-- Main content -->
<link rel="stylesheet" href="{{asset('css\form.css')}}">
<meta name="csrf-token" content="{{ csrf_token() }}">

<div class="card card-secondary container mt-5">
    <div class="card-header">
        <h3 class="card-title">Dynamic Form Builder</h3>
    </div>

    <div id="form-builder" class="mb-4">
        <div class="mb-3">
            <label for="field-type" class="form-label">Select Field Type:</label>
            <select id="field-type" class="form-select">
                <option value="text">Text</option>
                <option value="number">Number</option>
                <option value="email">Email</option>
                <option value="phone">Phone Number</option>
                <option value="select">Select</option>
            </select>
        </div> 
        {{-- <div class="mb-3">
            <label for="field-type" class="form-label">Select Data Type:</label>
            <select id="field-type" class="form-select">
                <option value="int">INT</option>
                <option value="varchar">VARCHAR</option>
                <option value="char">CHAR</option>
                <option value="">Phone Number</option>
                <option value="select">Select</option>
            </select>
        </div> --}}

        <div id="select-options" class="mb-3" style="display: none;">
            <label for="select-values" class="form-label">Enter Options (comma-separated):</label>
            <input type="text" id="select-values" class="form-control" placeholder="Option1, Option2, Option3">
            <div class="form-check mt-2">
                <input type="checkbox" id="multiselect" class="form-check-input">
                <label for="multiselect" class="form-check-label">Multiselect</label>
            </div>
        </div>

        <div class="mb-3">
            <label for="placeholder" class="form-label">Placeholder Text:</label>
            <input type="text" id="placeholder" class="form-control" placeholder="Enter placeholder">
        </div>

        <div class="form-check mb-3">
            <input type="checkbox" id="mandatory" class="form-check-input">
            <label for="mandatory" class="form-check-label">Mandatory</label>
        </div>

        <div class="mb-3">
            <label for="size" class="form-label">Input Size:</label>
            <input type="number" id="size" class="form-control" placeholder="Size (e.g., 20)">
        </div>

        <button id="add-field" class="btn btn-primary">Add Field</button>
    </div>
</div>
{{-- <h3>Form Preview:</h3>
<form id="dynamic-form" class="mb-5"></form> --}}


<script src="{{asset('Js\form.js')}}"></script>
@endsection