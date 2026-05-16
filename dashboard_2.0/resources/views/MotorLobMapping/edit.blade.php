@extends('layout.app', [
    'pageTitle' => 'MotorLobMapping',
    'pageHeader' => 'MotorLobMapping',
    'menu' => 'MotorLobMapping',
    'subMenu' => 'MotorLobMapping'
])

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
                    <a href="{{ route('motorLobMapping.index') }}" class="btn btn-dark">
                        <i class="fa-solid fa-arrow-left"></i> Back
                    </a>
                </div>

                <div class="card-body">
                    <form action="{{ route('motorLobMapping.update', $mapping->id) }}" method="POST">
                        @csrf
                        @method('PUT')

                        <div class="row">
                            <div class="col-md-6">
                                <label for="lob" class="required">LOB</label>
                                <select class="form-control" id="lob" name="lob" required>
                                    <option value="" disabled selected>Select LOB</option>
                                    @foreach($loblist as $lobs)
                                        <option value="{{ $lobs->lob }}" {{ (old('lob', $mapping->lob) == $lobs->lob) ? 'selected' : '' }}>{{ $lobs->lob }}</option>
                                    @endforeach
                                </select>
                            </div>

                            <div class="col-md-6">
                                <label for="motor_lob" class="required">Motor LOB</label>
                                <input type="text" class="form-control" id="motor_lob" name="motor_lob"
                                       value="{{ old('motor_lob', $mapping->motor_lob) }}" required>
                            </div>

                            <div class="col-md-6">
                                <label for="report_ob" class="required">Report OB</label>
                                <input type="text" class="form-control" id="report_ob" name="report_ob"
                                       value="{{ old('report_ob', $mapping->report_ob) }}" required>
                            </div>

                            <div class="col-md-6">
                                <label for="is_active" class="required">Is Active</label>
                                <select id="is_active" name="is_active" class="form-control" required>
                                    <option value="Y" {{ old('is_active', $mapping->is_active) == 'Y' ? 'selected' : '' }}>Yes</option>
                                    <option value="N" {{ old('is_active', $mapping->is_active) == 'N' ? 'selected' : '' }}>No</option>
                                </select>
                            </div>
                        </div>

                        <div class="card-footer mt-3">
                            <button type="submit" class="btn btn-dark">Update</button>
                        </div>
                    </form>
                </div>

            </div>
        </div>
    </div>
</div>
@endsection
