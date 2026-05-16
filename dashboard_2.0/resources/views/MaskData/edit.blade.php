@extends('layout.app', [
    'pageTitle' => 'Edit Mask Data',
    'pageHeader' => 'Edit Mask Data',
    'menu' => 'Mask Data',
    'subMenu' => 'Mask Data',
])

@section('content')
    <section class="content">
        <div class="container-fluid">

            <div class="row">
                <div class="col-md-8 offset-md-2"> 

                    <div class="card">
                        <div class="card-header">
                            <h5 class="mb-0">Edit Mask Data</h5>
                        </div>

                        <div class="card-body">

                            @if ($errors->any())
                                <div class="alert alert-danger">
                                    <ul class="mb-0">
                                        @foreach ($errors->all() as $error)
                                            <li>{{ $error }}</li>
                                        @endforeach
                                    </ul>
                                </div>
                            @endif

                            <form action="{{ route('MaskData.update', $data->id) }}" method="POST">
                                @csrf
                                @method('PUT')

                                <div class="form-group">
                                    <label><b>Field Name</b></label>

                                    <input type="text" name="field_name"
                                        class="form-control @error('field_name') is-invalid @enderror"
                                        placeholder="Enter Field Name" value="{{ old('field_name', $data->field_name) }}">

                                    @error('field_name')
                                        <div class="invalid-feedback">{{ $message }}</div>
                                    @enderror
                                </div>

                                <div class="col-md-6">
                                    <label for="status" class = "required">Status</label>
                                    <div class="ml-2">
                                        <div class="form-check form-check-inline">
                                            <input class="form-check-input" type="radio" name="status" id="active"
                                                value="Y" {{ old('status', $data->status) == 'Y' ? 'checked' : '' }}>
                                            <label class="form-check-label" for="active">Active</label>
                                        </div>
                                        <div class="form-check form-check-inline">
                                            <input class="form-check-input" type="radio" name="status" id="inactive"
                                                value="N" {{ old('status', $data->status) == 'N' ? 'checked' : '' }}>
                                            <label class="form-check-label" for="inactive">Inactive</label>
                                        </div>
                                    </div>
                                </div>

                                <div class="d-flex justify-content-between mt-4">

                                    <a href="{{ route('MaskData.index') }}" class="btn btn-secondary">
                                        Back
                                    </a>

                                    <button type="submit" class="btn btn-primary">
                                        Update
                                    </button>

                                </div>

                            </form>

                        </div>
                    </div>

                </div>
            </div>

        </div>
    </section>

@endsection
