<!DOCTYPE html>
<html lang="en">

<style>
    .button-group {
        display: flex;
        /* flex-wrap: wrap; */
        align-items: flex-start;
        /* display: flex;
    align-items: flex-start; */
    }

    .button-wrapper {
        display: flex;
        flex-direction: column;
        align-items: center;
        margin-bottom: 10px;
        /* Adjust as needed */
    }

    .button-link {
        margin-top: 5px;
        /* Adjust as needed */
    }

    .button-group .btn-link {
        margin-top: -0.5rem;
        /* Align links just below the buttons */
    }
    .error-text {
    color: red;
    }
</style>

<head>

    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    {{-- <title>{{ env('APP_NAME') ?? 'APP Name' }}</title> --}}

    <!-- Google Font: Source Sans Pro -->
    <link rel="stylesheet"
        href="https://fonts.googleapis.com/css?family=Source+Sans+Pro:300,400,400i,700&display=fallback">
    <!-- Font Awesome -->
    <link rel="stylesheet" href="{{env('APP_URL')}}/plugins/fontawesome-free/css/all.min.css">
    <!-- icheck bootstrap -->
    <link rel="stylesheet" href="{{env('APP_URL')}}/plugins/icheck-bootstrap/icheck-bootstrap.min.css">
    <!-- Theme style -->
    <link rel="stylesheet" href="{{env('APP_URL')}}/dist/css/adminlte.min.css">
</head>

<body class="hold-transition login-page">
    <div class="login-box">

        <div class="card card-outline card-primary">
            <div class="card-header text-center">

                <a href="{{env('APP_URL')}}/index2.html" class="h1"><b>{{ $broker_name }}</b></a>
            </div>
            <div class="card-body">
                <p class="login-box-msg">Sign in to start your session</p>
                @php
                    $option = explode(',', $sign_in_option);
                    $optionCount = count($option);
                @endphp
                <form action="{{ route('auth.login') }}" method="post">@csrf
                    <div class="input-group mb-3">
                        <input type="text" name="email" id="email" class="form-control"
                            placeholder="{{ $username }}" value="{{ old('email') }}" required>
                        <div class="input-group-append">
                            <div class="input-group-text">
                                <span class="fas fa-envelope"></span>
                            </div>
                        </div>
                        @error('email')
                            <span class="invalid-feedback d-inline">{{ $message }}</span>
                        @enderror
                    </div>
                    <div id="emailError" class="error-message"></div>
                    @if($broker->captacha_configure == 'On')
                    <div class="form-group">
                        <div class ='captcha' id='imagecaptcha'>
                            <span>{!!captcha_img('default')!!}</span>
                            <button type="button" class="btn btn-primary" class="reload" id="reload">↻</button>
                        </div>
                    </div>
					<div class="form-group">
                        <input type="text" name="captcha" id="captcha" class="form-control" placeholder="Enter Captcha">
                        @error('captcha')
                        <span class="invalid-feedback d-inline">{{ $message }}</span>
                    @enderror
                    <div id="captchaError" class="error-message"></div>
                    </div>
                    @endif
                    <div id="passwordInputContainer" class="input-group mb-3 mt-3"></div>

                    @if (in_array('', $option))
                        <div class="input-group mb-3">
                            <input type="text" name="password" id="password" class="form-control"
                                placeholder="{{ $password }}"required>
                            <div class="input-group-append">
                                <div class="input-group-text">
                                    <span id="lockBtn" class="fas fa-lock"></span>
                                </div>
                            </div>
                            @error('password')
                                <span class="invalid-feedback d-inline">{{ $message }}</span>
                            @enderror
                        </div>

                        <button type="submit" class="btn btn-primary mr-3" id='submitButton' value="Sign In">Sign
                            In</button>
                    @endif
                    <div class="button-group d-flex align-items-start" id='allbutton' >
                        {{-- @if (in_array('password', $option)) --}}
                            <div class="mr-3">
                                <input type="hidden" id="loginOption" name="loginOption">

                                <button type="button" class="btn btn-primary mb-2" id="passwordSubmit" value="Sign In"
                                    style="margin-left: 21px;">Password</button>


                                <a class="btn btn-link d-block" href="{{ route('login.with.forget.password') }}"
                                    id="forget-password">Forgot Password?</a>
                            </div>
                        {{-- @endif --}}

                        {{-- @if (in_array('email_otp', $option)) --}}
                            <button type="button" id="email_otp" class="btn btn-primary mb-2 otp_send"
                                style="margin-left: 5px;">OTP</button>
                        {{-- @endif --}}

                        {{-- @if (in_array('totp', $option))
                        <div class="mr-3">
                            <button type="submit" id="totp" class="btn btn-primary mb-2"
                                style="margin-left: 25px;">TOTP</button>

                            <a class="btn btn-link d-block request_qr" id="request_qr" style="display: none"
                                href="{{ route('admin.emailRequest') }}">Request QR Code</a>
                        </div>
                        @endif --}}
                    </div>

                    <div class="d-flex">
                        <button type="submit" class="btn btn-primary mr-3" id='submitButton' value="Sign In"
                            style="display:none">Sign In</button>
                        <button type="button" id="backBtn" class="btn btn-secondary" onclick="window.location.href='{{ route('login') }}'; window.location.reload();"
                            style="display:none">Back</button>

                    </div>

                </form>
            </div>
        </div>
    </div>
    <!-- jQuery -->
    <script src="{{env('APP_URL')}}/plugins/jquery/jquery.min.js"></script>
    <!-- Bootstrap 4 -->
    <script src="{{env('APP_URL')}}/plugins/bootstrap/js/bootstrap.bundle.min.js"></script>
    <!-- AdminLTE App -->
    <script src="{{env('APP_URL')}}/dist/js/adminlte.min.js"></script>
    <script src="https://code.jquery.com/jquery-3.5.1.slim.min.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/@popperjs/core@2.5.4/dist/umd/popper.min.js"></script>
    <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>
</body>
<script>
    $(document).ready(function() {
        function reloadCaptcha() {
        fetch('/reload-captcha')
            .then(response => response.json())
            .then(data => {
                document.querySelector('.captcha span').innerHTML = data.captcha;
            });
        }
        $('#totp').on('click', function() {
            var useremail = $('[name="email"]').val();
            var userInputCaptcha = $('[name="captcha"]').val();
            $('#loginOption').val('totp');
            fetch("{{ route('check.captcha') }}", {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRF-TOKEN': '{{ csrf_token() }}'
                },
                body: JSON.stringify({
                    'email': useremail,
                    'captcha': userInputCaptcha
                })

            })
            .then(response => response.json())
            .then(data => {
                if (data.status == 200) {
                $('#imagecaptcha').hide();
                $('#captcha').hide();
                $('#checkCaptcha').hide();
                window.location.href = "{{ route('totp') }}"
            } else {
                if (data.errors.email) {
                $('#emailError').text(data.errors.email.join(', ')).addClass('error-text');
                }
                if (data.errors.captcha) {
                    $('#captchaError').text(data.errors.captcha.join(', ')).addClass('error-text');
                    document.getElementById('reload').click();
                }
            }

                if (response.ok) {
                    return response.json();
                }
                throw new Error('Network response was not ok.');
            })
            .catch(error => {
                console.error('There was an error!', error);
            });
        });


        $('#passwordSubmit').on('click', function() {
            console.log('cosole')
        var useremail = $('[name="email"]').val();
        var userInputCaptcha = $('[name="captcha"]').val();

        $('#emailError').text('').removeClass('error-text');
        $('#captchaError').text('').removeClass('error-text');

        fetch("{{ route('check.captcha') }}", {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRF-TOKEN': '{{ csrf_token() }}'
                },
                body: JSON.stringify({
                    'email': useremail,
                    'captcha': userInputCaptcha // Replace with the actual username value
                })

            })
            .then(response => response.json())
            .then(data => {
                if (data.status == 200) {
                $('#allbutton').addClass('d-flex').show();
                $('#imagecaptcha').hide();
                $('#captcha').hide();
                $('#checkCaptcha').hide();
                $('#submitButton').css('display', 'block');
            $('#backBtn').css('display', 'block');
            $('#loginOption').val('password');
            var val = $('#loginOption').val(); // Retrieve the value
            if (val === 'password') {
                $('#passwordInputContainer').html(
                    `<div class="input-group">
                        <input type="password" name="password" id="password" class="form-control" placeholder="{{ $password }}">
                        <div class="input-group-append">
                            <div class="input-group-text">
                                <span id="lockBtn" class="fas fa-lock"></span>
                            </div>
                        </div>
                    </div>`
                );


                document.getElementById('request_qr').style.visibility = 'hidden';

                $('#forget-password').hide();
                $('#email_otp').hide();
                $('#totp').hide();
                $('#resend-otp').hide();
                $(this).hide(); // Hide the button

            }
            $('#lockBtn').click(function() {

                var passwordField = $('#password');
                console.log(passwordField.prop('type'));
                var lockBtn = $(this);

                if (lockBtn.hasClass("fas fa-lock")) {
                    lockBtn.removeClass('fas fa-lock');
                    lockBtn.addClass('fas fa-lock-open');
                    passwordField.prop('type', 'text');
                } else {
                    lockBtn.removeClass('fas fa-lock-open');
                    lockBtn.addClass('fas fa-lock');
                    passwordField.prop('type', 'password');
                }

                // Show the password input container if it's hidden
                $('#passwordInputContainer').show();
            });
            } else {
                if (data.errors.email) {
                $('#emailError').text(data.errors.email.join(', ')).addClass('error-text');
                }
                if (data.errors.captcha) {
                    $('#captchaError').text(data.errors.captcha.join(', ')).addClass('error-text');
                    reloadCaptcha();
                }
            }
                // })


                if (response.ok) {
                    return response.json();
                }
                throw new Error('Network response was not ok.');
            })
            .catch(error => {
                console.error('There was an error!', error);
            });

            // });
        });
        $('#email_otp').on('click', function() {
            $('#loginOption').val('email_otp');
        });
    });

    document.getElementById('reload').addEventListener('click', function () {
        fetch('/reload-captcha')
            .then(response => response.json())
            .then(data => {
                document.querySelector('.captcha span').innerHTML = data.captcha;
            });
    });
    $(".otp_send").click(function() {
        var useremail = $('[name="email"]').val();
        var userInputCaptcha = $('[name="captcha"]').val();
        sendOtp(useremail,userInputCaptcha);
    })

    function sendOtp(useremail,userInputCaptcha) {

        fetch("{{ route('send.otp') }}", {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRF-TOKEN': '{{ csrf_token() }}'
                },
                body: JSON.stringify({
                    'email': useremail,
                    'captcha': userInputCaptcha
                })

            })
            .then(response => response.json())
            .then(data => {
                if (data.status == 200) {
                $('#imagecaptcha').hide();
                $('#captcha').hide();
                $('#checkCaptcha').hide();
                window.location.href = "{{ route('otpVerify.page') }}"
            } else {
                if (data.errors.email) {
                $('#emailError').text(data.errors.email.join(', ')).addClass('error-text');
                }
                if (data.errors.captcha) {
                    $('#captchaError').text(data.errors.captcha.join(', ')).addClass('error-text');
                    document.getElementById('reload').click();

                }
            }

                if (response.ok) {
                    return response.json();
                }
                throw new Error('Network response was not ok.');
            })
            .catch(error => {
                console.error('There was an error!', error);
            });
    }

    function verifyOtp() {
        const otp = document.getElementById('otpInput').value;
        fetch("{{ route('verify.otp') }}", {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRF-TOKEN': '{{ csrf_token() }}'
                },
                body: JSON.stringify({
                    otp: otp
                })
            })
            .then(response => {
                if (response.ok) {
                    return response.json();
                }
                throw new Error('Network response was not ok.');
            })
            .then(data => {
                if (data.success) {
                    window.location.href =
                        "{{ route('otpVerify.page') }}"; // Redirect on successful OTP verification
                } else {
                    alert(data.message || 'Invalid User');
                }
            })
            .catch(error => {
                console.error('There was an error!', error);
            });
    }
</script>

</html>
