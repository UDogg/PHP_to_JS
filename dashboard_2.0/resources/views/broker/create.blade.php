@extends('layout.app', ['pageTitle' => 'Broker', 'pageHeader' => 'Broker', 'menu' => 'Broker', 'subMenu' => 'Broker'])
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
                    <a  href="{{ route('broker.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('broker.store') }}" method="POST" enctype="multipart/form-data">
                        @csrf
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="broker_name" class = "required">Broker Name</label>
                                        <input type="text" class="form-control" id="broker_name"
                                            placeholder="Enter Broker Name" name="broker_name" value="{{ old('broker_name') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="category" class = "required">Category</label>
                                        <input type="text" class="form-control" id="category"
                                            placeholder="Enter Category" name="category" value="{{ old('category') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="cin_no" class = "required">CIN No.</label>
                                        <input type="text" class="form-control" id="cin_no"
                                            placeholder="Enter CIN No." name="cin_no" value="{{ old('cin_no') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="contact_no" class = "required">Contact No</label>
                                        <input type="text" class="form-control" id="contact_no"
                                            placeholder="Enter Contact No" name="contact_no" value="{{ old('contact_no') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="email" class = "required">Email</label>
                                        <input type="text" class="form-control" id="email"
                                            placeholder="Enter Broker Email" name="email" value="{{ old('email') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="address" class = "required">Address</label>
                                        <input type="text" class="form-control" id="address"
                                            placeholder="Enter Broker Address" name="address" value="{{ old('address') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="irdia_registration_no" class = "required">IRDIA. Registration No</label>
                                        <input type="text" class="form-control" id="irdia_registration_no"
                                            placeholder="Enter Irdia Registration No" name="irdia_registration_no" value="{{ old('irdia_registration_no') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="favicon_icon" class = "required">Favicon Icon</label>
                                        <input type="file" class="form-control" id="favicon_icon"
                                             name="favicon_icon" value="{{ old('favicon_icon') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="logo" class = "required">Broker Logo</label>
                                        <input type="file" class="form-control" id="logo"
                                            name="logo" value="{{ old('logo') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="front_logo" class = "required">Front Logo</label>
                                        <input type="file" class="form-control" id="front_logo"
                                            name="front_logo" value="{{ old('front_logo') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="sign_in_option" class = "required">Sign In Option</label>
                                        <select name="sign_in_option[]" multiple="" data-placeholder="please select values" class="select2 select2-hidden-accessible form-control" style="width: 100%;"  tabindex="-1" aria-hidden="true">
                                            <option value="">Nothing Selected</option>
                                            <option value="password">Password</option>
                                            <option value="email_otp">OTP</option>
                                            <option value="totp">2FA Authentication</option>
                                        </select>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="captacha_configure" class="required">Captcha Configure</label>
                                        <select name="captacha_configure" class="form-control" required>
                                            <option value="">Select Option</option>
                                            <option value="On" {{ (old('captacha_configure') == 'On') ? 'selected' : '' }}>On</option>
                                            <option value="Off" {{ (old('captacha_configure') == 'Off') ? 'selected' : '' }}>Off</option>
                                        </select>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="is_email" class="required">Is Email</label>
                                        <select name="is_email" class="form-control" required>
                                            <option value="">Select Option</option>
                                            <option value="Y" {{ (old('is_email') == 'Y') ? 'selected' : '' }}>Yes</option>
                                            <option value="N" {{ (old('is_email') == 'N') ? 'selected' : '' }}>No</option>
                                        </select>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="is_sms" class="required">Is SMS</label>
                                        <select name="is_sms" class="form-control" required>
                                            <option value="">Select Option</option>
                                            <option value="Y" {{ (old('is_sms') == 'Y') ? 'selected' : '' }}>Yes</option>
                                            <option value="N" {{ (old('is_sms') == 'N') ? 'selected' : '' }}>No</option>
                                        </select>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="marquee" class="required">Marquee</label>
                                        <select name="marquee" class="form-control" required>
                                            <option value="">Select Option</option>
                                            <option value="Y" {{ (old('marquee') == 'Y') ? 'selected' : '' }}>Yes</option>
                                            <option value="N" {{ (old('marquee') == 'N') ? 'selected' : '' }}>No</option>
                                        </select>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="default_otp" class="required">Default Otp</label>
                                        <select name="default_otp" class="form-control" required>
                                            <option value="">Select Option</option>
                                            <option value="Y" {{ (old('default_otp') == 'Y') ? 'selected' : '' }}>Yes</option>
                                            <option value="N" {{ (old('default_otp') == 'N') ? 'selected' : '' }}>No</option>
                                        </select>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="master_otp" class = "required">Master Otp</label>
                                        <input type="text" class="form-control" id="master_otp"
                                            placeholder="Enter master_otp" name="master_otp" value="{{ old('master_otp') }}" onkeyup="this.value = this.value.replace(/\D/g, '').slice(0, 6);">
                                    </div>

                                    <div class="col-md-6">
                                        <label for="status" class = "required">Status</label>
                                        <div class="ml-2">
                                            <div class="form-check form-check-inline">
                                                <input class="form-check-input" type="radio" name="status" id="active" value="Y" checked>
                                                <label class="form-check-label" for="active">Active</label>
                                            </div>
                                            <div class="form-check form-check-inline">
                                                <input class="form-check-input" type="radio" name="status" id="inactive" value="N">
                                                <label class="form-check-label" for="inactive">Inactive</label>
                                            </div>
                                        </div>
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
