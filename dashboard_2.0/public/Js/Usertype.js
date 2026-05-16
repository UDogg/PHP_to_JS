$(function(){
       // Check if the checkbox is checked
       function statusSetVal()
       {

           if ($('#activeId').is(':checked')) {
               $('[name="is_active"]').val('Y')
            } else {
                $('[name="is_active"]').val('N')
            }
        }
        statusSetVal()
        $("#activeId").click(statusSetVal)
    $(".addBtn").click(function(){
        const usertype = $("[name='UserType']");
        const uTypeIdent = $("[name='Userident']");
        const is_updt = $("[name='is_update']").val();
        const is_active = $("[name='is_active']").val();

        if(usertype.val() == '')
        {
            toastr.error("Please Enter User Type")
            usertype.focus()
            return false
        }
        if(uTypeIdent.val() == '' && is_updt == '')
        {
            toastr.error("Please Enter User Identifier")
            uTypeIdent.focus()
            return false
        }
        const formData = $("[name='UserTypeMaster']").serialize();
        if(is_updt == 'Y')
        {
            var url = "api/UserType/update"
            var method = "PUT"
        }
        else{
            // url= "api/UserTypes/createUserType", 
            url= "createUserType", 
            method= "POST",
            headers={
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
              }
        }
        $.ajax({
            type:method,
            url:url,
            data:formData,
            headers:{
              'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            success:function(response){
                if(response.status == 'true')
                {
                    toastr.success(response.message)
                    $("[name='UserTypeMaster']").reset()
                }
                else
                {
                    toastr.error(response.message)
                }
            },
            error:function(error){
                console.log(error)
                if(error.status == 422)
                {
                    toastr.error(error.responseJSON.errors.UserType[0])
                }
                else
                {
                    toastr.error("some error occured please try again after some time")
                }
            }
        })

    })
    $(".edt_btn").click(function(){
        const id = $(this).attr('uid')
        var isActive = $(this).data('is-active');
        const cardTitleText = $(this).closest('.card').find('.card-title').text();
        $("[name='UserType']").val(cardTitleText)
        $("[name='is_update']").val('Y')
        if (isActive === 'Y') {
            $('#activeId').prop('checked', true);
            $('#checkIsactive').val('Y');
        } else {
            $('#activeId').prop('checked', false);
            $('#checkIsactive').val('N');
        }
        $("[name='id']").val(id)
        $("[name='Userident']").closest('.col-sm-4').hide()
    })
    $(".del_btn").click(function(){
        const current = $(this);
            const id = current.attr('uid')
        $.ajax({
            url: 'api/UserType/delete',
            type: 'POST',
            headers: {
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            data: {
                id: id
            },
            success: function(response) {
                if (response.status == 'true') {
                    toastr.success(response.message);
                    current.closest('.col-sm-3').remove();
                } else {
                    toastr.error(response.message);
                    return false;
                }
            },
            error: function(xhr, status, error) {
                // Handle error
            }
        });
    })

    $(".edit-section-field").click(function () {
        var id = $(this).data("id");
        var name = $(this).data("name"); // usertype's name

        console.log('id:', id);
        console.log('name:', name);
       
        $("#usertype_id").val(id);
        $("#editusername").val(name).trigger('change');

        $("#editUserFieldModal").modal("show");
    });

    $("#editUsertypeForm").submit(function (event) {
        event.preventDefault();

        const token = $("[name='apitoken']").val();
        var formData = {
            _token: token,
            id: $('#usertype_id').val(),
            name: $('#editusername').val(),
            reset_password: $('#reset_password').val() || null,
        };

        $.ajax({
            url: APP_URL + "/api/updateusertype",
            type: "PUT", 
            data: formData,
            headers: {
                Authorization: "Bearer " + token,
            },
            success: function (response) {
                alert(response.message);
                location.reload();
            },
            error: function (xhr) {
                alert("Error: " + (xhr.responseJSON?.message || "Unknown error"));
            },
        });
    });
})
