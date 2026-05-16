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
            <div class="card-body">
                <p class="login-box-msg">Enter email id to receive mail.</p>
                <form action="" method="post">@csrf

                    <div class="input-group mb-3">
                        <input id="requested_email" type="email" name="requested_email" class="form-control"
                            placeholder="Please Enter Your Email">
                        <div class="input-group-append">
                            <div class="input-group-text">
                                <span class="fas fa-envelope"></span>
                            </div>
                        </div>
                    </div>
                    @error('requested_email')
                                        <span class="invalid-feedback d-inline">{{ $message }}</span>
                                    @enderror
                    <div class="mt-3">
                        <button class="btn btn-primary"
                            href="#">Submit</button>
                        <button type="button" class="btn btn-secondary" onclick="window.history.back();">Back</button>
                    </div>
                </form>
            </div>
        </div>
    </div>

    <script src="{{env('APP_URL')}}/plugins/jquery/jquery.min.js"></script>
    <!-- Bootstrap 4 -->
    <script src="{{env('APP_URL')}}/plugins/bootstrap/js/bootstrap.bundle.min.js"></script>
    <!-- AdminLTE App -->
    <script src="{{env('APP_URL')}}/dist/js/adminlte.min.js"></script>
</body>




<script src="https://code.jquery.com/jquery-3.7.1.min.js"
            integrity="sha256-/JqT3SQfawRcv/BIHPThkBvs0OEvtFFmqPF/lYI/Cxo=" crossorigin="anonymous"></script>
<script>
    $(document).ready(function() {
                $("form")[0].reset()
            });
            $("#otp").css('letter-spacing', '20px');

            function validateNumberInput(input) {
                input.value = input.value.replace(/[^0-9]/g, '');
            }
            var timeLeft = 60;
            var elem = document.getElementById('timer');
            var timerId = setInterval(countdown, 1000);

            function countdown() {
                if (timeLeft == -1) {
                    clearTimeout(timerId);
                    elem.setAttribute('hidden', true)
                    $('#resendOtpBtn').attr('hidden', false);
                } else {
                    elem.innerHTML = timeLeft + ' seconds remaining';
                    timeLeft--;
                }
            }
</script>

</html>
