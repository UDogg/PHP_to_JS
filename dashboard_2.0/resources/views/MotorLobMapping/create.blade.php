@extends('layout.app', ['pageTitle' => 'MotorLobMapping', 'pageHeader' => 'MotorLobMapping','menu' => 'MotorLobMapping','subMenu' => 'MotorLobMapping'])
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
                        <a href="{{ route('motorLobMapping.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('motorLobMapping.store') }}" method="POST">
                            @csrf
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="lob" class="required">LOB</label>
                                            <select class="form-control" id="lob" name="lob" required>
                                                <option value="" disabled selected>Select LOB</option>
                                                @foreach($loblist as $lobs)
                                                    <option value="{{ $lobs->lob }}" {{ old('lob') == $lobs->lob ? 'selected' : '' }}>{{ $lobs->lob }}</option>
                                                @endforeach
                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="motor_lob" class = "required">Motor Lob</label>
                                            <input type="text" class="form-control" id="motor_lob"
                                                placeholder="Enter Motor Lob" name="motor_lob"
                                                value="{{  old('motor_lob') }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="report_ob" class = "required">Report OB</label>
                                            <input type="text" class="form-control" id="report_ob" placeholder="Enter Report OB" name="report_ob" value="{{  old('report_ob') }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="is_active" class = "required">Is Active</label>
                                            <select id="is_active" name="is_active" class="form-control" required>
                                                <option value="" {{ old('is_active') == '' ? 'selected' : '' }}>Is Active</option>
                                                <option value="Y" {{ old('is_active') == 'Y' ? 'selected' : '' }}>Yes</option>
                                                <option value="N" {{ old('is_active') == 'N' ? 'selected' : '' }}>No</option>
                                            </select>
                                        </div>

                                </div>
                            </div>
                            <!-- /.card-body -->
                            <div class="card-footer">
                                <button type="submit" class="btn btn-dark">Submit</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
        </div>
    </div>

@endsection
