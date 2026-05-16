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

        <div class="card card-outline card-primary">
            <div class="card-header text-center">
                <a href="{{env('APP_URL')}}/index2.html" class="h1"><b>{{ env('APP_NAME') ?? 'APP Name' }}</b></a>
            </div>
            <div class="card-body">
                <p class="login-box-msg">Please Enter your Password</p>

                <form action="{{ route('auth.resetPassword') }}" method="post">@csrf
                    <div class="input-group mb-3">
                        <input id="newpassword" type="password" name="newpassword" class="form-control"
                            placeholder="Password">
                        <div class="input-group-append">
                            <div class="input-group-text">
                                <span id="lockBtn" class="fas fa-lock"></span>
                            </div>
                        </div>
                        @error('newpassword')
                            <span class="invalid-feedback d-inline">{{ $message }}</span>
                        @enderror
                    </div>
                    <div class="input-group mb-3">
                        <input id="confirmpassword" type="password" name="confirmpassword" class="form-control"
                            placeholder="Confirm Password">
                        <div class="input-group-append">
                            <div class="input-group-text">
                                <span id="lockIcon" class="fas fa-lock"></span>
                            </div>
                        </div>
                        @error('confirmpassword')
                            <span class="invalid-feedback d-inline">{{ $message }}</span>
                        @enderror
                    </div>
                    <input type="hidden" name="user_id" class="form-control" id="user_id"
                        value="{{ $user_id }}">
                    <!-- Validation Text -->
                    <div class="mb-3">
                        <p class="text-muted">
                            Password requirements:
                        <ul class="text-muted">
                            <li>Minimum of 8 characters</li>
                            <li>At least one special character</li>
                            <li>At least one uppercase letter</li>
                            <li>At least one number</li>
                            <li>Example: Password@1</li>
                        </ul>
                        </p>
                    </div>
                    <!-- /.col -->
                    <div class="input-group mb-3">
                        <button type="button" class="btn btn-primary flex-grow-1 mr-1" id="submitButton">Submit</button>
                    </div>
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
<script src="{{asset('Js/resetpassword.js')}}"></script>
</html>
