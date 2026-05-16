@extends('layout.app', ['pageTitle' => 'Session Time', 'pageHeader' => 'Session Time', 'menu' => 'Session Time', 'subMenu' => 'Session'])
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
                        <a href="{{ route('broker.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('broker.update', $broker) }}" method="POST" enctype="multipart/form-data">
                            @csrf @method('PUT')
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="broker_name" class = "required">Broker Name</label>
                                            <input type="text" class="form-control" id="broker_name"
                                                placeholder="Enter Broker Name" name="broker_name"
                                                value="{{ $broker->broker_name }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="category" class = "required">Category</label>
                                            <input type="text" class="form-control" id="category"
                                                placeholder="Enter Broker Name" name="category"
                                                value="{{ $broker->category }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="cin_no" class = "required">Cin No.</label>
                                            <input type="text" class="form-control" id="cin_no"
                                                placeholder="Enter Broker Name" name="cin_no" value="{{ $broker->cin_no }}"
                                                required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="contact_no" class = "required">Contact No</label>
                                            <input type="text" class="form-control" id="contact_no"
                                                placeholder="Enter Contact No" name="contact_no"
                                                value="{{ $broker->contact_no }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="email" class = "required">Email</label>
                                            <input type="text" class="form-control" id="email"
                                                placeholder="Enter Broker Email" name="email" value="{{ $broker->email }}"
                                                required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="address" class = "required">Address</label>
                                            <input type="text" class="form-control" id="address"
                                                placeholder="Enter Broker Address" name="address"
                                                value="{{ $broker->address }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="irdia_registration_no" class = "required">Irdia Registration
                                                No</label>
                                            <input type="text" class="form-control" id="irdia_registration_no"
                                                placeholder="Enter Irdia Registration No" name="irdia_registration_no"
                                                value="{{ $broker->irdia_registration_no }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="sign_in_option" class = "required">Sign In Option</label>
                                            <select name="sign_in_option[]" multiple="" data-placeholder="please select values" class="select2 select2-hidden-accessible form-control" style="width: 100%;"  tabindex="-1" aria-hidden="true">
                                                <option value="password" {{ in_array('password', old('sign_in_option', explode(',', $broker->sign_in_option ?? ''))) ? 'selected' : '' }}>Password</option>
                                                <option value="email_otp" {{ in_array('email_otp', old('sign_in_option', explode(',', $broker->sign_in_option ?? ''))) ? 'selected' : '' }}>OTP</option>
                                                <option value="totp" {{ in_array('totp', old('sign_in_option', explode(',', $broker->sign_in_option ?? ''))) ? 'selected' : '' }}>2FA Authentication</option>
                                            </select>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="favicon_icon">Favicon Icon</label>
                                            <input type="file" class="form-control" id="favicon_icon" name="favicon_icon">
                                            @if($broker->favicon_icon)
                                                <img src="{{ Storage::url($broker->favicon_icon) }}" alt="Favicon Icon" width="100">
                                            @endif
                                        </div>

                                        <div class="col-md-6">
                                            <label for="logo">Broker Logo</label>
                                            <input type="file" class="form-control" id="logo" name="logo">
                                            @if($broker->logo)
                                                <img src="{{ Storage::url($broker->logo) }}" alt="Broker Logo" width="100">
                                            @endif
                                        </div>
                                        <div class="col-md-6">
                                            <label for="logo">Front Logo</label>
                                            <input type="file" class="form-control" id="front_logo" name="front_logo">
                                            @if($broker->front_logo)
                                                <img src="{{ Storage::url($broker->front_logo) }}" alt="Broker Front Logo" width="100">
                                            @endif
                                        </div>
                                        <div class="col-md-6">
                                            <label for="status" class = "required">Status</label>
                                            <div class="ml-2">
                                                <div class="form-check form-check-inline">
                                                    <input class="form-check-input" type="radio" name="status" id="active" value="Y" {{ old('status', $broker->status) == 'Y' ? 'checked' : '' }}>
                                                    <label class="form-check-label" for="active">Active</label>
                                                </div>
                                                <div class="form-check form-check-inline">
                                                    <input class="form-check-input" type="radio" name="status" id="inactive" value="N" {{ old('status', $broker->status) == 'N' ? 'checked' : '' }}>
                                                    <label class="form-check-label" for="inactive">Inactive</label>
                                                </div>
                                            </div>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="captacha_configure" class="required">Captcha Configure</label>
                                            <select name="captacha_configure" class="form-control" required>
                                                <option value="On" {{ (old('captacha_configure', $broker->captacha_configure) == 'On') ? 'selected' : '' }}>On</option>
                                                <option value="Off" {{ (old('captacha_configure', $broker->captacha_configure) == 'Off') ? 'selected' : '' }}>Off</option>

                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="is_email" class="required">Is Email</label>
                                            <select name="is_email" class="form-control" required>

                                                <option value="Y" {{ (old('is_email', $broker->is_email) == 'Y') ? 'selected' : '' }}>Yes</option>
                                                <option value="N" {{ (old('is_email', $broker->is_email) == 'N') ? 'selected' : '' }}>No</option>
                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="is_sms" class="required">Is SMS</label>
                                            <select name="is_sms" class="form-control" required>

                                                <option value="Y" {{ (old('is_sms', $broker->is_sms) == 'Y') ? 'selected' : '' }}>Yes</option>
                                                <option value="N" {{ (old('is_sms', $broker->is_sms) == 'N') ? 'selected' : '' }}>No</option>
                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="marquee" class="required">Marquee</label>
                                            <select name="marquee" class="form-control" required>

                                                <option value="Y" {{ (old('marquee', $broker->marquee) == 'Y') ? 'selected' : '' }}>Yes</option>
                                                <option value="N" {{ (old('marquee', $broker->marquee) == 'N') ? 'selected' : '' }}>No</option>
                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="default_otp" class="required">Default Otp</label>
                                            <select name="default_otp" class="form-control" >

                                                <option value="Y" {{ (old('default_otp', $broker->default_otp) == 'Y') ? 'selected' : '' }}>Yes</option>
                                                <option value="N" {{ (old('default_otp', $broker->default_otp) == 'N') ? 'selected' : '' }}>No</option>
                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="master_otp" class = "required">Master Otp</label>
                                            <input type="text" class="form-control" id="master_otp"
                                                placeholder="Enter Master Otp" name="master_otp"
                                                value="{{ $broker->master_otp }}" onkeyup="this.value = this.value.replace(/\D/g, '').slice(0, 6);">
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
    <!-- Bootstrap CSS -->
    <link href="https://maxcdn.bootstrapcdn.com/bootstrap/4.5.2/css/bootstrap.min.css" rel="stylesheet">
    <!-- Bootstrap Select CSS -->
    <link href="https://cdnjs.cloudflare.com/ajax/libs/bootstrap-select/1.13.18/css/bootstrap-select.min.css" rel="stylesheet">
    <!-- jQuery -->
    <script src="https://ajax.googleapis.com/ajax/libs/jquery/3.5.1/jquery.min.js"></script>
    <!-- Bootstrap JS -->
    <script src="https://maxcdn.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>
    <!-- Bootstrap Select JS -->
    <script src="https://cdnjs.cloudflare.com/ajax/libs/bootstrap-select/1.13.18/js/bootstrap-select.min.js"></script>
    <script>
        $(document).ready(function() {
            $('.select2').select2({
        closeOnSelect: false
    })
        });
    </script>
@endsection
