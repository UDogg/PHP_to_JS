@extends('layout.app', ['pageTitle' => 'OTP', 'pageHeader' => 'OTP Time', 'menu' => 'OTP Time', 'subMenu' => 'OTP'])
@section('content')
    <style>
        input[type="otpTime"] {
            width: 100px;
            text-align: center;
        }
    </style>
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
                        <a href="{{ route('otp.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('otp.store') }}" method="POST">
                            @csrf
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="otp_validation_time" class = "required">OTP Validation Time</label>
                                            <input type="text" class="form-control" id="otp_validation_time"
                                                name="otp_validation_time" placeholder="HH:MM:SS"
                                                value="{{ old('otp_validation_time')  }}" required>

                                        </div>
                                        <div class="col-md-6">
                                            <label for="resend_otp_time" class = "required">Resend OTP Time</label>
                                            <input type="text" class="form-control" id="resend_otp_time"
                                                placeholder="HH:MM:SS" name="resend_otp_time"
                                                value="{{  old('resend_otp_time') }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="broker_name" class = "required">Broker Name</label>
                                            <select id="broker_name" name="broker_name" class="form-control" required>

                                                <option value="" {{ old('broker_name') == '' ? 'selected' : '' }}>
                                                    Select Broker</option>

                                                @foreach ($otpData as $otpData)
                                                    <option value="{{ $otpData }}"
                                                        {{ old('broker_name') == $otpData ? 'selected' : '' }}>
                                                        {{ $otpData }}
                                                    </option>
                                                @endforeach

                                            </select>
                                        </div>
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
