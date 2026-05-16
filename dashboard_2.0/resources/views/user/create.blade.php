@extends('layout.app', ['pageTitle' => 'User', 'pageHeader' => 'User', 'menu' => 'User', 'subMenu' => 'User'])
@section('content')
<link href="https://cdn.jsdelivr.net/npm/select2@4.0.13/dist/css/select2.min.css" rel="stylesheet" />

<div class="container">
    <div class="row">
        <div class="col-12">
            <div class="card">
                <div class="card-header">
                    @if(session('message'))
                        <div class="alert alert-{{ session('class') }}">
                            {{ session('message') }}
                        </div>
                    @endif
                    <a  href="{{ route('user.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('user.store') }}" method="POST" name="usercreation">
                        @csrf
                        <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="username" class = "required">User Name</label>
                                        <input type="text" class="form-control" id="username"
                                            placeholder="Enter User Name" name="username" value="{{ old('username') }}" required>
                                            @error('username')
                                                <span class="invalid-feedback d-inline">{{ $message }}</span>
                                            @enderror
                                    </div>
                                    <div class="col-md-6">
                                        <label for="name" class = "required">Name</label>
                                        <input type="text" class="form-control" id="name"
                                            placeholder="Enter Name" name="name" value="{{ old('name') }}" required>
                                            @error('name')
                                                <span class="invalid-feedback d-inline">{{ $message }}</span>
                                            @enderror
                                    </div>
                                </div>

                            </div>
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="mobile" class="required">Mobile</label>
                                        <input type="tel" class="form-control" id="mobile"
                                            placeholder="Enter Mobile Number" name="mobile" value="{{ old('mobile') }}"
                                            maxlength="10" title="Please enter exactly 10 digits" inputmode="numeric" required>
                                        @error('mobile')
                                            <span class="invalid-feedback d-inline">{{ $message }}</span>
                                        @enderror
                                    </div>
                                    <div class="col-md-6">
                                        <label for="email" class = "required">Email</label>
                                        <input type="email" class="form-control" id="email"
                                            placeholder="Enter Email Address" name="email" value="{{ old('email') }}" required>
                                            @error('email')
                                                <span class="invalid-feedback d-inline">{{ $message }}</span>
                                            @enderror
                                    </div>
                                    <input type="hidden" name="secret" class="form-control" id="secret" value="{{$qrCode['secret']}}">
                                </div>
                            </div>
                            <div class="form-group">                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="address" class = "required">Address</label>
                                        <input type="text" class="form-control" id="address"
                                            placeholder="Enter User Address" name="address" value="{{ old('address') }}" required>
                                            @error('address')
                                                <span class="invalid-feedback d-inline">{{ $message }}</span>
                                            @enderror
                                    </div>
                                    <div class="col-md-6">
                                        <label for="pincode" class = "required">Pincode</label>
                                        <input type="text" class="form-control" id="pincode"
                                            placeholder="Enter Pincode" name="pincode" value="{{ old('pincode') }}"
                                            maxlength="6" title="Please enter exactly 6 digits" required>
                                        @error('pincode')
                                        <span class="invalid-feedback d-inline">{{ $message }}</span>
                                        @enderror
                                    </div>
                                </div>
                            </div>
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label class="required">Gender</label><br>
                                        <div class="form-check form-check-inline">
                                            <input type="radio" class="form-check-input" id="male" value="M" name="gender" required>
                                            <label for="male" class="form-check-label">Male</label>
                                        </div>
                                        <div class="form-check form-check-inline">
                                            <input type="radio" class="form-check-input" id="female" value="F" name="gender">
                                            <label for="female" class="form-check-label">Female</label>
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="required">Status</label><br>
                                        <div class="form-check form-check-inline">
                                            <input type="radio" class="form-check-input" id="active" value="Y" name="status" required>
                                            <label for="active" class="form-check-label">Active</label>
                                        </div>
                                        <div class="form-check form-check-inline">
                                            <input type="radio" class="form-check-input" id="inactive" value="N" name="status">
                                            <label for="inactive" class="form-check-label">In Active</label>
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="required">User Types</label><br>
                                        <div class="form-check form-check-inline">
                                            <select class="custom-select" name="getusertype" >
                                                <option value=""> select User Type</option>
                                                @foreach($getusertype as $userType)
                                                    <option value="{{ $userType->id }}">{{ $userType->name }}</option>
                                                @endforeach
                                            </select>
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="required">Employee Code</label><br>
                                        <div class="form-check form-check-inline">
                                            <input type="text" maxlength="10" class="form-control" id="empCodeId" name="employeeCode">
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="required">Select LOB</label>
                                        <select class="custom-select select2" name="lob_id[]" multiple>
                                            <option value="">Select LOB</option>
                                            @foreach($getLob as $Lob)
                                            <option value="{{ $Lob->id }}">{{ $Lob->lob }}</option>
                                            @endforeach
                                        </select>
                                    </div>

                                    <div class="col-md-6">
                                        <label class="required">Role</label><br>
                                        <div class="form-check form-check-inline">
                                            <select class="custom-select" name="role_id">
                                                <option value=""> select User role</option>
                                                @foreach($getRole as $role)
                                                <option value={{ $role->id }}>{{ $role->name }}</option>
                                                @endforeach
                                            </select>
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="required">Qualification</label><br>
                                        <div class="form-check form-check-inline">
                                            <select class="custom-select" name="qualification" >
                                                <option value=""> select User role</option>
                                                <option value=1>ssc</option>
                                                <option value=2>hsc</option>
                                                <option value=4>graduation</option>
                                            </select>
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="">Reporting To</label><br>
                                        <div class="form-check form-check-inline">
                                            <select class="custom-select" name="reportingto" >
                                                <option value=""> select Reporting To</option>
                                            </select>
                                        </div>
                                    </div>

                                </div>
                            </div>
                            <div class="form-group">
                            </div>
                        </div>
                        <!-- /.card-body -->
                        <div class="card-footer">
                            <button type="submit" class="btn btn-dark" name="sb_btn">Submit</button>
                        </div>
                    </form>
                </div>
            </div>
        </div>
    </div>
</div>
<script src="https://cdn.jsdelivr.net/npm/select2@4.0.13/dist/js/select2.min.js"></script>
<script>
    $(document).ready(function() {
        $('.select2').select2({
            placeholder: "Select LOBs",
            allowClear: true
        });
    });
</script>
{{-- <script>

    function handle_eye(event, id) {
        var element = event.target;
        var input = document.getElementById(id)
        if (element.classList.contains('fa-eye')) {
            element.classList.remove('fa-eye');
            element.classList.add('fa-eye-slash');
            input.setAttribute('type', 'password');
        } else {
            element.classList.remove('fa-eye-slash');
            element.classList.add('fa-eye');
            input.setAttribute('type', 'text');
        }
    }
</script>
<script src="{{asset('Js/user.js')}}"></script>
<script>
    function checkFuntion() {
        var char = $('#password').val();
        if (char.length == '0') {
            $('#1,#2,#3,#4').css('color', 'red');
        }

        var hasUpperCaseLetter = /[A-Z]/g;
        var hasLowerCaseLetter = /[a-z]/g;
        var hasAtLeastOneNumber = /[0-9]/g;
        var hasAtLeastOneSymbol = /[@$!%*#?&]/g;

        if (char.match(hasUpperCaseLetter)) {
            $('#1').css('color', 'green');
        } else if (!char.match(hasUpperCaseLetter)) {
            $('#1').css('color', 'red');
        }
        if (char.match(hasLowerCaseLetter)) {
            $('#2').css('color', 'green');
        } else if (!char.match(hasLowerCaseLetter)) {
            $('#2').css('color', 'red');
        }
        if (char.match(hasAtLeastOneNumber)) {
            $('#3').css('color', 'green');
        } else if (!char.match(hasAtLeastOneNumber)) {
            $('#3').css('color', 'red');
        }
        if (char.match(hasAtLeastOneSymbol)) {
            $('#4').css('color', 'green');
        } else if (!char.match(hasAtLeastOneSymbol)) {
            $('#4').css('color', 'red');
        }
    }
    document.addEventListener('DOMContentLoaded', function () {
            const askOtpCheckbox = document.getElementById('askOtp');
            const authMethodSelect = document.getElementById('authMethod');

            function toggleAuthMethod() {
                authMethodSelect.disabled = !askOtpCheckbox.checked;
            }

            // Initialize the state on page load
            toggleAuthMethod();

            // Add event listener to the checkbox
            askOtpCheckbox.addEventListener('change', toggleAuthMethod);
        });
</script> --}}
@endsection
