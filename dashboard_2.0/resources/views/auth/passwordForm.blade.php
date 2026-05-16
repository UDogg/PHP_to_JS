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
        <!-- /.login-logo -->
        @if ($errors->any())
            <div class="alert alert-danger">
                <ul class="list">
                    @foreach ($errors->all() as $error)
                        <li>{{ $error }}</li>
                    @endforeach
                </ul>
            </div>
        @endif
        <div class="card card-outline card-primary">
            <div class="card-header text-center">
                <a href="{{env('APP_URL')}}/index2.html" class="h1"><b>{{ env('APP_NAME') ?? 'APP Name' }}</b></a>
            </div>
            <div class="card-body">
                <p class="login-box-msg">Sign in to start your session</p>

                <form action="{{ route('login.with.otp.post') }}" method="post">@csrf
                    <div>
                        <label for="password">Password</label>
                        <input type="password" name="password" id="password" class="form-control" placeholder="password" required>
                    </div>
                    <div>
                        <label for="password_confirmation">Confirm Password</label>
                        <input type="password" name="password_confirmation" id="password_confirmation" class="form-control" placeholder="password_confirmation" required>
                    </div>

                    <!-- /.col -->
                    <div class="input-group mb-3">
                        <button type="submit" class="btn btn-primary">Set Password</button>
                        {{-- <button type="submit" class="btn btn-primary flex-grow-1 mr-1">Send OTP</button> --}}

                    </div>

                    {{-- <div class="row">
                        <div class="col-8">
                            <div class="icheck-primary">
                                <input type="checkbox" id="remember" name="remember">
                                <label for="remember">
                                    Remember Me
                                </label>
                            </div>
                        </div>

                        <!-- /.col -->
                    </div> --}}
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
</script>

</html>
