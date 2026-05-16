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
                {{-- $broker = Broker::select('broker_name')->first();
        $broker_name = $broker->broker_name; --}}

                <h1>Fyntune</h1>
                {{-- <a href="{{env('APP_URL')}}/index2.html" class="h1"><b>{{ env('APP_NAME') ?? 'APP Name' }}</b></a> --}}
            </div>
            <div class="card-body">
                <p class="login-box-msg">Please Enter Email to reset your Password</p>

                <form action="" method="post">@csrf
                    <div class="input-group mb-3">
                        <input id="email" type="email" name="email" class="form-control"
                            placeholder="Please Enter Your Email" required>
                        <div class="input-group-append">
                            <div class="input-group-text">
                                <span class="fas fa-envelope"></span>
                            </div>
                        </div>
                    </div>
                    @error('email')
                                        <span class="invalid-feedback d-inline">{{ $message }}</span>
                                    @enderror
                    {{-- <input type="hidden" name="user_id" class="form-control" id="user_id" value="{{$user_id}}"> --}}

                    <!-- /.col -->
                    <div class="mt-3">
                        <button type="button" class="btn btn-primary email_send">Submit</button>
                        <button type="button" class="btn btn-secondary" onclick="window.history.back();">Back</button>
                    </div>
                </form>
            </div>
            <!-- /.card-body -->
        </div>

        {{-- Modal for reset password --}}
        <div class="modal fade" id="resetPasswordModal"style="display: none;" aria-hidden="true">
            <div class="modal-dialog">
                <div class="modal-content">

                    <div class="modal-body">
                        <p class="text-danger">If the email address is registered, a password reset link will be sent to the registered email address.</p>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" id="closeButton" data-dismiss="modal">Close</button>

                    </div>
                </div>
            </div>
        </div>

        {{-- Modal for invalid user --}}
        <div class="modal fade" id="invalidUserModal"style="display: none;" aria-hidden="true">
            <div class="modal-dialog">
                <div class="modal-content">

                    <div class="modal-body">
                        <p class="text-danger">If the email address is registered, a password reset link will be sent to the registered email address.</p>
                                            </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>

                    </div>
                </div>
            </div>
        </div>
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
    $('#closeButton').on('click', function() {
        window.location.href = "{{ route('login') }}";
    });
});
    $(".email_send").click(function() {
        var email = $('[name="email"]').val();
        sendEmail(email);
    })
    function sendEmail(email) {
        fetch("{{ route('send-email') }}", {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRF-TOKEN': '{{ csrf_token() }}'
                },
                body: JSON.stringify({
                    email: email // Replace with the actual username value
                })

            })

            .then(response => response.json())
            .then(data => {
                if (data.status) {

                    $('#resetPasswordModal').modal('show');
                }
        else {

                    $('#invalidUserModal').modal('show');
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

</script>

</html>
