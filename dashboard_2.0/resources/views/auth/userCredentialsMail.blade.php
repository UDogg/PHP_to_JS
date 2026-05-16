<!-- resources/views/emails/otp.blade.php -->

<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>OTP Email</title>
    <style>
        body {
            font-family: 'Arial', sans-serif;
            background-color: #f4f4f4;
            color: #333;
        }

        .container {
            max-width: 600px;
            margin: 0 auto;
            padding: 20px;
            background-color: #fff;
            border-radius: 8px;
            box-shadow: 0 0 10px rgba(0, 0, 0, 0.1);
        }

        h2 {
            color: #3498db;
        }

        p {
            line-height: 1.6;
        }

        .otp-code {
            font-size: 24px;
            font-weight: bold;
            color: #ff0000;
        }
    </style>
</head>
<body>
    <div class="container">
        <b>{{$body}}</b>
    <h2>This is your one time password</h2>
    <p>Password for Login:</p>
    <p class="password">{{ $password }}</p>
    <p>Please Click on below Link to login and reset your passowrd.</p>
    {{ env('FRONTEND_URL') }}

    </div>


</body>
</html>
