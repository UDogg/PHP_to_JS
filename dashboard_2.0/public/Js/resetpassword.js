$(function(){
$(document).ready(function() {
    $('#submitButton').click(function() {
        const user= $('[name="user_id"]').val();
        const token = $('[name="_token"]').val();
        const password = $('[name="newpassword"]').val();
        const confirm_password = $('[name="confirmpassword"]').val();
        const data = {
            password: password ,
            confirm_password : confirm_password,
            user_id: user
        };
        $.ajax({
            url: 'http://127.0.0.1:8000/api/reset-password',
            type: 'POST',
            headers: {
                'Accept': '*/*',
                'Accept-Language': 'en-US,en;q=0.9',
                'Connection': 'keep-alive',
                'Content-Type': 'application/json',
                'Cookie': 'XSRF-TOKEN='+ token,
            },
            data: JSON.stringify(data),
            success: function(response) 
            {
                window.location.href = 'http://127.0.0.1:8000/login';
            },
            error: function(xhr, status, error) {
                toastr.error('Something went wrong')
                // Handle error here
            }
        });
    });
});
        $('#lockBtn').click(function() {
    
            var passwordField = $('#newpassword');
            var confirmPasswordField = $('#confirmpassword');
    
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
    
        });
        $('#lockIcon').click(function() {
    
            var passwordField = $('#newpassword');
            var confirmPasswordField = $('#confirmpassword');
    
            console.log(passwordField.prop('type'));
    
            var lockIcon = $(this);
    
            if (lockIcon.hasClass("fas fa-lock")) {
                lockIcon.removeClass('fas fa-lock');
                lockIcon.addClass('fas fa-lock-open');
                confirmPasswordField.prop('type', 'text');
            } else {
                lockIcon.removeClass('fas fa-lock-open');
                lockIcon.addClass('fas fa-lock');
                confirmPasswordField.prop('type', 'password');
            }
    
        });
})