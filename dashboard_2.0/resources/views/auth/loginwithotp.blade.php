<!DOCTYPE html>
<html lang="en">

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
                <p class="login-box-msg">Verify OTP to start your session</p>

                <form id="otpForm" action="{{ route('verify.otp') }}" method="post">
                    @csrf
                    <div class="form-group">
                        <label for="otp">Enter OTP</label>
                        <input type="text" id="otp" name="otp" class="form-control">
                        @error('otp')
                                                <span class="invalid-feedback d-inline">{{ $message }}</span>
                                            @enderror
                        <span id="timer"></span>
                    </div>
                    <button type="submit" class="btn btn-primary">Verify OTP</button>
                    <button type="button" class="btn btn-secondary" id="backBtn">Back</button>
                    <a class="btn btn-link otp_send" href="#" id="resend-otp" hidden>{{ __('Resend OTP') }}</a>
                </form>

            </div>
            <!-- /.card-body -->
        </div>
        <!-- /.card -->
    </div>
    <!-- /.login-box -->

    <!-- jQuery -->
    <script src="{{env('APP_URL')}}/plugins/jquery/jquery.min.js"></script>
    <!-- Bootstrap 4 -->
    <script src="{{env('APP_URL')}}/plugins/bootstrap/js/bootstrap.bundle.min.js"></script>
    <!-- AdminLTE App -->
    <script src="{{env('APP_URL')}}/dist/js/adminlte.min.js"></script>
</body>
<script>
    $(document).ready(function() {
    $('#backBtn').on('click', function() {
        window.location.href = "{{ route('console') }}";
    });
});
    $('#lockBtn').click(function() {
        if ($(this).hasClass("fas fa-lock")) {
            $(this).removeClass('fas fa-lock');
            $(this).addClass('fas fa-lock-open');
            $('#password').prop('type', 'text');
        } else {
            $(this).removeClass('fas fa-lock-open');
            $(this).addClass('fas fa-lock');
            $('#password').prop('type', 'password');
        }
    });

    function verifyOtp() {

        const otp = document.getElementById('otp').value;

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
            .then(response => response.json())
            .then(data => {
                if (data.success) {
                    window.location.href = "{{ route('dashboard') }}";
                } else {
                    alert(data.message || 'Failed to verify OTP');
                }
            })
            .catch(error => {
                console.error('There was an error!', error);
            });
    }
    document.getElementById('resend-otp').addEventListener('click', function(e) {
        e.preventDefault();
        fetch('{{ route('resend.otp') }}', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
                'X-CSRF-TOKEN': '{{ csrf_token() }}'
            },
            body: JSON.stringify({
                email: "{{$email}}"
            })

        })
        .then(response => response.json())
        .then(data => {
            if (data.success) {
                alert(data.message);
            } else {
                alert(data.message);
            }
        });
    });
    var timeLeft = 60;
            var elem = document.getElementById('timer');
            var resendOtpBtn = document.getElementById('resend-otp');
            var timerId = setInterval(countdown, 1000);

            function countdown() {
            if (timeLeft == 0) {
                clearTimeout(timerId);
                elem.setAttribute('hidden', true);
                resendOtpBtn.removeAttribute('hidden');
            } else {
                elem.innerHTML = 'Resend OTP in ' + timeLeft + ' seconds';
                timeLeft--;
            }
        }

        countdown();

            $('#email_otp').on('click', function() {
            $('#loginOption').val('email_otp');
        });
    // });


    $(".otp_send").click(function() {
        var useremail = $('[name="email"]').val();
        sendOtp(useremail);
    })

    function sendOtp(useremail) {

        fetch("{{ route('send.otp') }}", {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRF-TOKEN': '{{ csrf_token() }}'
                },
                body: JSON.stringify({
                    email: useremail // Replace with the actual username value
                })

            })
            .then(response => response.json())
            .then(data => {
                if (data.success) {
                    window.location.href = "{{ route('otpVerify.page') }}?email=" +
                        useremail // Redirect to the OTP form
                } else {
                    alert('Invalid User');
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
