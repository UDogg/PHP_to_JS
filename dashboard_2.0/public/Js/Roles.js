$(function(){
    function getRoles(usertype= 0 ,toastr) {
        $("#IdRole").html("");
        $("#ReportingRoleID").html("");
        $.ajax({
            url:'api/roles/list',
            method:'GET',
            headers:{
              'Authorization':'Bearer '+ $("[name='apitoken']").val()
            },
            data:{
              usertype : usertype
            },
            success:function(response){
                if(response.status == 'true')
                {
                    var data = response.data;
                    var options = '';
                    $.each(data,function(index,item){
                        options = $('<option></option>').val(item.id).text(item.name);
                        options.appendTo("#IdRole");
                        options.clone().appendTo('#ReportingRoleID')
                    })
                }
                else
                {
                    toastr.error("Error Getting List Of Roles")
                    return false;
                }
            }
        })
    }
    getRoles('',toastr);

    function getUsers() {
        $.ajax({
            url: 'api/users/list',
            method: 'GET',
            data:{
                usertype : $("[name='UsertypeID']").val()
            },
            headers: {
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            success: function(response) {
                if (response.status == 'true') {
                    var data = response.data;
                    var options = '';
                    $("[name='user_id']").html("");
                    $.each(data, function(index, item) {
                        options = $('<option></option>').val(item.id).text(item.name);
                        options.appendTo("[name='user_id']");
                    })
                } else {
                    toastr.error("Error Getting List Of Users")
                    return false;
                }
            },
            error: function(xhr, status, error) {
                console.error("Error getting users:", error);
            }
        });
    }
    getUsers();
    $("[name='UsertypeID']").change(function() {
        const id = $(this).val();
        getRoles(id);
        getUsers();
    })
 $(".add_role").click(function(){
    const roleVal = $("#Role_id").val();
    const formData = $("[name='RoleMaster']").serialize();
     $.ajax({
         url: 'api/roles/create',
         method: 'POST',
         data: formData,
         headers: {
             'Authorization': 'Bearer ' + $("[name='apitoken']").val()
         },
         success: function(response) {
             if (response.status == 'true') {
                 toastr.success(response.message);
                 $("[name='RoleMaster']")[0].reset();
                 getRoles(toastr);
             } else {
                 toastr.error(response.message);
             }
         },
         error: function(xhr, status, error) {
             if (xhr.status == 422) {
                 toastr.error(xhr.responseJSON.errors.RoleName[0]);
             } else {
                 toastr.error("Some error occurred. Please try again after some time.");
             }
         }
     });
 })
    $(".del_btn").click(function(){
        const current = $(this);
       const id = current.attr('uid')
        $.ajax({
            url : "api/roles/delete/",
            method : "post",
            data : {
                id : id
            },
            headers: {
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            success : function(response){
                if(response.status == 'true'){
                    toastr.success(response.message)
                    current.closest(".col-sm-3").remove();
                }else{
                    toastr.error(response.message)
                }
            },
            error : function(error){
                if(error.status == 422){
                    toastr.error(error.responseJSON.errors.RoleName[0])
                }else{
                    toastr.error("some error occured please try again after some time")
                }
            }

        })
    })
    $(".AssignRole").click(function(){
        const role = $("[name='role_id']")
        const user = $("[name='user_id']")
        if(role.val() == '')
        {
            toastr.error("Please Select Role Name")
            return false
        }
        if(user.val() == '')
        {
            toastr.error("Please Select User Name")
            return false
        }
        const formData = {
            role_id:role.val(),
            user_id:user.val(),
            // _token:$("[name='_token']").val()
        };
        $.ajax({
            url:"api/roles/assign",
            method:"POST",
            data:JSON.stringify(formData),
            contentType:"application/json",
            dataType: "json",
            headers: {
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            success:function(response){
                if(response.status == 'true')
                {
                    toastr.success(response.message)
                }
                else
                {
                    toastr.error(response.message)
                    return false
                }
            },
            error:function(error){
                if(error.status == 422)
                {
                    toastr.error(error.responseJSON.errors.RoleName[0])
                    return false
                }
                else
                {
                    toastr.error("some error occured please try again after some time")
                }
            }

        })
    })
    // roles list api
    $.ajax({
        url: 'api/roles/list',
        method: 'GET',
        headers: {
            'Authorization': 'Bearer ' + $("[name='apitoken']").val()
        },
        success: function (data) {

            $.each(data.data, function (key, value) {
                $('select[name="reportingrole"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
            });
            }
    });
    // usertype list api
    $.ajax({
        url: 'api/UserType/list',
        method: 'GET',
        headers: {
            'Authorization': 'Bearer ' + $("[name='apitoken']").val()
        },
        success: function (data) {

            $.each(data.data, function (key, value) {
                $('select[name="usertype"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
            });
        }
    })

    $(".edt_btn").click(function(){
        $("#edit_modal").modal('show')
        const roleId = $(this).attr('uid')
        const oldsertype = $(this).attr('utype')
        const oldreportingrole = $(this).attr('rptrole')
        $('[name="usertype"] option:contains("' + oldsertype + '")').prop('selected', true);
        if(oldreportingrole != '')
        {
            $('[name="reportingrole"] option:contains("' + oldreportingrole + '")').prop('selected', true);
        }
        else {
            $('[name="reportingrole"]').val("");
        }
        const oldroleName = $(this).closest('.card-body').find('.card-title').text();
        $("#roleName").val(oldroleName)
        $("[name='RoleId']").val(roleId)
        $(".cls_mdl").click(function(){
            const newrolename = $("#roleName").val();
            if(newrolename == '')
            {
                toastr.error("Please Enter Role Name")
                $("#roleName").focus()
                return false
            }
            const usertypeId = $("[name='usertype']").val();
            if(usertypeId == '')
            {
                toastr.error("Please Select User Type")
                return false
            }
            const reportingroleId = $("[name='reportingrole']").val();
            // if(reportingroleId == '')
            // {
            //     toastr.error("Please Select Reporting Role")
            //     return false
            // }

            $.ajax({
                url: 'api/roles/edit',
                method: 'PUT',
                headers: {
                    'Authorization': 'Bearer ' + $("[name='apitoken']").val()
                },
                data: {
                    id: roleId,
                    RoleName: oldroleName,
                    UsertypeID: usertypeId,
                    ReportingRole: reportingroleId
                },
                success: function (data) {
                    if(data.status == 'true')
                    {
                        toastr.success(data.message)
                        $("#edit_modal").modal('hide')
                        location.reload()
                    }
                }
            })
        })
    })

})
