$(function(){
    var allPerms = '';
    $.ajax({url :'api/PermissionAccess/GetAll',
        method:'GET',
        headers:{
            'Authorization': 'Bearer ' + $("[name='apitoken']").val()
        },
        success: function (response) {
            if (response.status == '200') {
                var data = response.data
                $.each(data,function(key,value){
                    $("[name='permissionList']").append('<option value="'+ value.id +'">' + value.name + '</option>');
                })
                $.each(data,function(key,value){

                    var newCard = $(".cardd").clone().show().appendTo(".data_row");
                    newCard.find(".card-title").text("Permission name: " + value.name);

                })
            }
            else
            {

                toastr.error(response.message)
                allPerms =  false
                return false;
            }

        }
    })
    $.ajax({url :'api/ConfigSettingsList',
        method:'GET',
        headers:{
            'Authorization': 'Bearer ' + $("[name='apitoken']").val()
        },
        success: function (response) {
            if (response.status == '200')
            {
                var data = response.data
                $.each(data,function(key,value){
                    $("[name='configList']").append('<option value="'+ value.id +'">' + value.name + '</option>');
                })
            }
            else
            {

                toastr.error(response.message)
                return false;
            }

        }

        })

  $(".add_perm").click(function(){
    const is_upt = $("[name='is_updt']").val()
    const apitoken = $("[name='apitoken']").val()
    if($("[name='permission']").val() == '')
    {
        toastr.error("Please Enter Permission Name")
        return false
    }
    var formdata = $("[name='perMaster']").serialize();
    if (is_upt == 'Y')
    {
    //         update here permission name
    }
    else
    {
        $.ajax({url:'api/PermissionAccess/Create',
            type:'POST',
            data:formdata,
            headers:{
                'Authorization': 'Bearer ' + apitoken
            },

        }).done(function (response)
        {
            if(response.status == '200')
            {

                toastr.success("Permission is Created SuccessFully")
            }
        }).fail(function(error){

            if(error.status == 422)
            {
                toastr.error(error.responseJSON.errors.permission[0])
            }
            else
            {
                toastr.error("some error occured please try again after some time")
            }
        })
    }

})
    $(".mappermission").click(function(){

        const apitoken = $("[name='apitoken']").val()
        const permissionId = $("[name='permissionList']").val()
        const configId = $("[name='configList']").val()

        if(permissionId == '')
        {
            toastr.error("Please Select Permission")
            return false
        }

        if(configId == '')
        {
            toastr.error("Please Select Config")
            return false
        }

        $.ajax({url:'api/PermissionAccess/MapPermission',
            type:'POST',
            data:{'permissionId':permissionId,'configId':configId},
            headers:{
                'Authorization': 'Bearer ' + apitoken
            },

        }).done(function (response)
        {
            if(response.status == '200')
            {

                toastr.success("Permission is Created SuccessFully")
            }
            else
            {

                toastr.error(response.message)
                return false
            }

        }).fail(function(error){
            if(error.status == 422)
            {
                toastr.error(error.responseJSON.errors.permission[0])
            }
            else
            {
                toastr.error("some error occured please try again after some time")
            }
        })
    })
})
$(document).ready(function() {
    $.ajax({
        url: 'api/PermissionAccess/ListMapPermission',
        method: 'GET',
        headers: {
            'Authorization': 'Bearer ' + $("[name='apitoken']").val()
        },
        success: function(response) {
            // Ensure response has the expected structure
            if (response && response.data) {
                var permissions = response.data; 
                console.log(response);
    
                // Prepare HTML for the table rows
                var rows = '';
                permissions.forEach(function(permission) {
                    rows += '<tr>' +
                                '<td>' + (permission.value || '') + '</td>' +  // Handle empty values
                                '<td>' + (permission.key || '') + '</td>' +    // Handle empty values
                            '</tr>';
                });
    
                // Insert rows into the table body
                content = sanitizeHtml(rows);
                $('#permissionsTable tbody').html(content);
            } else {
                console.error('Unexpected response structure:', response);
            }
        },
        error: function(xhr, status, error) {
            console.error('Error fetching data:', error);
        }
    });
    
});
