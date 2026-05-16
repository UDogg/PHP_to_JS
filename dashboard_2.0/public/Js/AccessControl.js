$(function () {
    $('.select2').select2({
        closeOnSelect: false
    });

    $("#UsertypeID").prop('disabled', true);
    $("#permissionSelect").prop('disabled', true);
    $(".GiveAccess").prop('disabled', true);

    function listRoles(usertypeId) {
        $.ajax({
            url: 'api/roles/list',
            type: 'GET',
            data: { usertype: usertypeId },
            headers: {
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            success: function (response) {
                const data = response.data;

                $("#UsertypeID").html('<option value="">Select</option>');
                $("#rolesTable tbody").empty();

                $.each(data, function (key, value) {
                    $("#UsertypeID").append('<option value="' + value.id + '">' + value.name + '</option>');
                    $("#rolesTable tbody").append(
                        '<tr>' +
                        '<td>' + value.id + '</td>' +
                        '<td>' + value.name + '</td>' +
                        '</tr>'
                    );
                });
                $("#UsertypeID").prop('disabled', false);
            },
            error: function (xhr, status, error) {
                toastr.error("Some error occurred. Please try again later.");
            }
        });
    }

    $("#usertypeFilter").change(function () {
        const usertypeId = $(this).val();
        if (usertypeId) {
            listRoles(usertypeId);
        } else {
            $("#UsertypeID").prop('disabled', true).html('<option value="">Select</option>');
            $("#permissionSelect").prop('disabled', true).html('<option value="">Select</option>');
            $(".GiveAccess").prop('disabled', true);

            $("#rolesTable tbody").empty();
            $("#permissionsTable tbody").empty();
        }
    });

    $("#UsertypeID").change(function () {
        const roleId = $(this).val();
        const usertypeId = $("#usertypeFilter").val();
        const usertypeName = $("#usertypeFilter option:selected").text();
        const roleName = $("#UsertypeID option:selected").text();
        if (roleId) {
            $("#permissionSelect").prop('disabled', false);
            $(".GiveAccess").prop('disabled', false);

            $.ajax({
                url: 'api/AccessControl/getDataByFilter',
                type: 'POST',
                data: {
                    usertype_id: usertypeId,
                    usertype_name: usertypeName,
                    role_id: roleId,
                    role_name: roleName
                },
                headers: {
                    'Authorization': 'Bearer ' + $("[name='apitoken']").val()
                },
                success: function (response) {
                    const data = response.data;

                    $("#permissionsTable tbody").empty();
                    let srNo = 1;
                    $.each(data, function (key, value) {
                        let rolesHtml = '';
                        rolesHtml += `<button class="btn btn-secondary btn-sm revoke_permission" p_id="${value.permission_id}">${value.role_name}</button> `;

                        $("#permissionsTable tbody").append(
                            '<tr>' +
                            '<td>' + (srNo++) + '</td>' +
                            '<td>' + value.permission_name + '</td>' +
                            '<td>' + rolesHtml + '</td>' +
                            '<td>' +
                            '<button class="btn btn-secondary delete" data-id="' + value.permission_id + '">Delete</button>' +
                            '</td>' +
                            '</tr>'
                        );
                    });


                    if (response.status == 'success') {
                        toastr.success(response.message);
                    } else {
                        toastr.error(response.message);
                    }
                },
                error: function (xhr, status, error) {
                    toastr.error("Some error occurred. Please try again later.");
                }
            });

        } else {

            $("#permissionSelect").prop('disabled', true).html('<option value="">Select</option>');
            $(".GiveAccess").prop('disabled', true);

            $("#permissionsTable tbody").empty();
        }
    });

    // Function to handle the edit and delete buttons
    function attachEditDeleteListeners() {
        $(".edit").off('click').on('click', function() {
            const permissionId = $(this).data('id');

            // AJAX request to get the permission details for editing
            $.ajax({
                url: 'api/AccessControl/getPermissionDetails',
                type: 'POST',
                data: { permission_id: permissionId },
                headers: {
                    'Authorization': 'Bearer ' + $("[name='apitoken']").val()
                },
                success: function(response) {
                    if (response.status === 'success') {
                        // Populate the edit modal with the response data
                        content = sanitizeHtml(response.html);
                        $('#editPermissionModal .modal-title').text('Edit Permission');
                        $('#editPermissionModal .modal-body').html(content); // Adjust based on response format

                        // Show the modal
                        $('#editPermissionModal').modal('show');

                        // Handle form submission inside the modal if needed
                        $('#editPermissionModal').find('.save-changes').off('click').on('click', function() {
                            var updatedData = $('#editPermissionModal form').serialize();
                            $.ajax({
                                url: 'api/AccessControl/updatePermission', // Adjust the URL as needed
                                type: 'POST',
                                data: updatedData,
                                headers: {
                                    'Authorization': 'Bearer ' + $("[name='apitoken']").val()
                                },
                                success: function(response) {
                                    if (response.status === 'success') {
                                        toastr.success("Permission updated successfully");
                                        $('#editPermissionModal').modal('hide');
                                        // Reload the data if necessary
                                        $("#UsertypeID").change(); // Or any other function to refresh data
                                    } else {
                                        toastr.error(response.message);
                                    }
                                },
                                error: function(xhr, status, error) {
                                    toastr.error("Some error occurred. Please try again later.");
                                }
                            });
                        });
                    } else {
                        toastr.error(response.message);
                    }
                },
                error: function(xhr, status, error) {
                    toastr.error("Some error occurred. Please try again later.");
                }
            });
        });

        $(".delete").off('click').on('click', function() {
            const permissionId = $(this).data('id');

            // Show confirmation modal
            $('#editPermissionModal .modal-title').text('Confirm Delete');
            $('#editPermissionModal .modal-body').text('Are you sure you want to delete this permission?');
            $('#editPermissionModal').modal('show');

            // Handle the confirm delete button
            $('#editPermissionModal').find('.cnf_delete').off('click').on('click', function() {
                $.ajax({
                    url: 'api/AccessControl/deletePermission', // Adjust the URL as needed
                    type: 'POST',
                    data: { permission_id: permissionId },
                    headers: {
                        'Authorization': 'Bearer ' + $("[name='apitoken']").val()
                    },
                    success: function(response) {
                        if (response.status === 'success') {
                            toastr.success("Permission deleted successfully");
                            $('#editPermissionModal').modal('hide');
                            // Reload the data if necessary
                            $("#UsertypeID").change(); // Or any other function to refresh data
                        } else {
                            toastr.error(response.message);
                        }
                    },
                    error: function(xhr, status, error) {
                        toastr.error("Some error occurred. Please try again later.");
                    }
                });
            });
        });

        // Handle revoke permission button
        $(".revoke_permission").off('click').on('click', function() {
            const permissionId = $(this).attr('p_id');
            const roleId = $(this).attr('r_id');
            // Handle revoke functionality here
            toastr.error("Revoking permission " + permissionId + " from role " + roleId);
        });
    }

    $(".GiveAccess").click(function () {
        if ($("[name='permission_id[]']").val() == '') {
            toastr.error("Please Enter Permission Name");
            return false;
        }
        if ($("[name='role_id']").val() == '') {
            toastr.error("Please Enter Role Name");
            return false;
        }

        var formdata = $("[name='AssignRole']").serialize();
        $.ajax({
            url: 'api/AccessControl/giveAccess',
            data: formdata,
            method: 'POST',
            headers: {
                'Authorization': 'Bearer ' + $("[name='apitoken']").val()
            },
            success: function (response) {
                if (response.status == 'true') {
                    toastr.success("Permission is Assigned Successfully");
                    setTimeout(function () {
                        window.location.reload();
                    }, 1000);
                }
            }
        });
    });

    $.ajax({
        url: 'api/UserType/filterUserTypeList',
        type: 'GET',
        headers: {
            'Authorization': 'Bearer ' + $("[name='apitoken']").val()
        },
        success: function (response) {
            const data = response.data;
            // Append a static option first
            $("#usertypeFilter").append('<option value="5">Customer</option>');
            $.each(data, function (key, value) {
                $("#usertypeFilter").append('<option value="' + value.id + '">' + value.name + '</option>');
            });
        },
        error: function (xhr, status, error) {
            toastr.error("Some error occurred. Please try again later.");
        }
    });

    $('.delete').on('click', function () {
        const token = $('[name="_token"]').val();
        let id = $(this).data('id');

        if (confirm('Are you sure you want to delete this data?')) {
            $.ajax({
                url: 'api/AccessControl/deleteData',
                method: 'POST',
                data: {
                    permission_id: id
                },
                headers: {
                    'Authorization': 'Bearer ' + $("[name='apitoken']").val()
                },
                success: function (data) {
                    if(data.status == 200){
                        toastr.success('column Deleted Successfully');
                    }
                    location.reload();
                }
            });
        }
    });
   
    $(".revoke_permission").on('click', function() {
        const permissionId = $(this).attr('p_id');
        const roleId = $(this).attr('r_id');
        const roleName = $(this).text().trim();
        $("#permissionId").val(permissionId);
        $("#roleId").val(roleId);
        $("#roleName").val(roleName);
        $("#editModal").modal("show");
        
    });

    $("#revokeUserPermission").on('click', function () {
        const permissionId = $("#permissionId").val();
        const roleId = $("#roleId").val();
        const roleName = $("#roleName").val();
        const apiToken = $("[name='apitoken']").val();

        $.ajax({
            url: 'api/AccessControl/revokePermission', 
            type: 'POST',
            data: {
                permission_id: permissionId,
                role_id: roleId,
                role_name: roleName,
            },
            headers: {
                'Authorization': 'Bearer ' + apiToken,
            },
            success: function (response) {
                toastr.success("Permission " + permissionId + " revoked successfully from role " + roleName);
                location.reload();
            },
            error: function (xhr, status, error) {
                toastr.error("Error revoking permission. Please try again.");
            }
        });
        $("#editModal").modal("hide");
    });

});
