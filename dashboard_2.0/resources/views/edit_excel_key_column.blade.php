@extends('layout.app', ['pageTitle' => 'Excel Key Column', 'pageHeader' => 'Excel Key Column', 'menu' => 'Excel Key Column', 'subMenu' => 'Excel Key Column'])
@section('content')
    <div class="container">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        @if ($errors->any())
                            <div class="alert alert-danger">
                                <ul class="list">
                                    @foreach ($errors->all() as $error)
                                        <li>{{ $error }}</li>
                                    @endforeach
                                </ul>
                            </div>
                        @endif
                        <a href="{{ route('excel_column.index') }}" class="btn btn-dark"><i
                                class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('excel_column.update', $column->excel_key_master_id) }}" method="POST">
                            @csrf
                            @method('PUT') 
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="policystatus_column_master_id">Policy Status Column Master</label>
                                            <select name="policystatus_column_master_id" class="form-control">
                                                <option value="">Select Policy Status Column</option>
                                                @foreach ($policyStatus as $status)
                                                    <option value="{{ $status->id }}"
                                                        {{ old('policystatus_column_master_id', $column->policystatus_column_master_id) == $status->id ? 'selected' : '' }}>
                                                        {{ $status->column_name }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="lob_id" class="required">Lob</label>
                                            <input type="text" class="form-control" id="lob_id" name="lob_id"
                                                value="{{ old('lob_id', $column->lob_id) }}" required>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="excel_column_name" class="required">Excel Column Name</label>
                                            <input type="text" class="form-control" id="excel_column_name"
                                                name="excel_column_name"
                                                value="{{ old('excel_column_name', $column->excel_column_name) }}" required>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="sequence" class="required">Sequence</label>
                                            <input type="number" class="form-control" id="sequence" name="sequence"
                                                value="{{ old('sequence', $column->sequence) }}" required>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="is_visible" class="required">Is Visible</label>
                                            <select name="is_visible" class="form-control">
                                                <option value="Y"
                                                    {{ old('is_visible', $column->is_visible) == 'Y' ? 'selected' : '' }}>
                                                    Yes</option>
                                                <option value="N"
                                                    {{ old('is_visible', $column->is_visible) == 'N' ? 'selected' : '' }}>
                                                    No</option>
                                            </select>
                                        </div>
                                    </div>
                                </div>
                            </div>
                            <!-- /.card-body -->
                            <div class="card-footer">
                                <button type="submit" class="btn btn-dark">Update</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
        </div>
    </div>
@endsection
