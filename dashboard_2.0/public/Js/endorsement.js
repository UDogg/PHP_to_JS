
$(document).ready(function () {
    // Create Status
    $('#submitBtn').on('click', function (e) {
        var token = $('meta[name="csrf-token"]').attr('content');
        var formData = {
            _token: token,
            status_name: $('#status_name').val(),

        };
        $.ajax({
            url: 'api/create',
            method: 'POST',
            data: JSON.stringify(formData),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'X-CSRF-TOKEN': token,
                'X-Requested-With': 'XMLHttpRequest'
            },

            success: function (response) {
                if (response.status == 200) {
                    location.reload();
                }
            },
            error: function (xhr) {
                let errors = xhr.responseJSON.errors;
                let errorMessage = '';
                $.each(errors, function (key, value) {
                    errorMessage += value[0] + '\n';
                });
                alert(errorMessage);
            }
        });
    });

    // Edit Status
    $('.edit-status').on('click', function () {
        var id = $(this).data('id');
        var name = $(this).data('name');
                $('#edit_status_id').val(id);
        $('#edit_status_name').val(name);
            });

    // Save changes for Status
    $('#editStatusForm').on('submit', function (e) {
        e.preventDefault();
        var id = $(this).attr('data-id');
        $.ajax({
            url: 'api/update',
            method: 'PUT',
            id: id,
            data: $(this).serialize(),
            success: function (response) {
                // Handle success
                $('#editStatusModal').modal('hide');
                location.reload(); // Refresh the page to see changes
            },
            error: function (xhr) {
                // Handle errors
                alert('Something went wrong!');
            }
        });
    });
    // Delete Status
    $('.delete-status').on('click', function () {
        var id = $(this).attr('data-id');

        var token = $('meta[name="csrf-token"]').attr('content');

        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/delete',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    id: id
                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'X-CSRF-TOKEN': token,
                    'X-Requested-With': 'XMLHttpRequest'
                },

                success: function (response) {
                    // Handle success
                    location.reload(); // Refresh the page to see changes
                },
                error: function (xhr) {
                    // Handle errors
                    alert('Something went wrong!');
                }
            });
        }
    });



    // create service support type
    $('#submitBtnSst').on('click', function (e) {
        var token = $('meta[name="csrf-token"]').attr('content');
        var formData = {
            _token: token,
            service_support_type: $('#service_support_type').val(),

        };
        $.ajax({
            url: 'api/create',
            method: 'POST',
            data: JSON.stringify(formData),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'X-CSRF-TOKEN': token,
                'X-Requested-With': 'XMLHttpRequest'
            },
            success: function (response) {
                if (response.status == 200) {
                    location.reload();
                }
            },
            error: function (xhr) {
                let errors = xhr.responseJSON.errors;
                let errorMessage = '';
                $.each(errors, function (key, value) {
                    errorMessage += value[0] + '\n';
                });
                alert(errorMessage);
            }
        });
    });

    // Edit sst
    $('.edit-sst').on('click', function () {
        var id = $(this).data('id');
        var name = $(this).data('name');
        $('#edit_sst_id').val(id);
        $('#edit_sst_name').val(name);
    });

    // Save changes for Status
    $('#editSstForm').on('submit', function (e) {
        e.preventDefault();
        var id = $(this).attr('data-id');
        console.log(id);
        $.ajax({
            url: 'api/updateSst',
            method: 'PUT',
            id: id,
            data: $(this).serialize(),
            success: function (response) {
                // Handle success
                $('#editSstModal').modal('hide');
                location.reload(); // Refresh the page to see changes
            },
            error: function (xhr) {
                // Handle errors
                alert('Something went wrong!');
            }
        });
    });

    // Delete SST
    $('.delete-sst').on('click', function () {
        var id = $(this).attr('data-id');

        var token = $('meta[name="csrf-token"]').attr('content');
        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/deleteSst',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    id: id
                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'X-CSRF-TOKEN': token,
                    'X-Requested-With': 'XMLHttpRequest'
                },
                success: function (response) {
                    // Handle success
                    location.reload(); // Refresh the page to see changes
                },
                error: function (xhr) {
                    // Handle errors
                    alert('Something went wrong!');
                }
            });
        }
    });

    // create section
    $.ajax({
        url: 'api/lob/list', // Assuming this is the correct URL
        method: 'GET',
        dataType: 'json',
        success: function(response) {
            if(response.status == 200) {
                let lobDropdown = $('#fetchLob');
                $.each(response.data, function(index, item) {
                    // Append each LOB name as an option
                    var option = '<option value="' + item.lob_name + '">' + item.lob_name + '</option>';
                    lobDropdown.append(option);
                });
            }
        },
        error: function(xhr) {
            console.error("Error fetching LOBs:", xhr);
        }
    });

    $('#submitBtnSection').on('click', function (e) {


        $.ajax({
            url: 'api/createSection',
            method: 'POST',
            data: $('#sectionForm').serialize(),
            success: function (response) {
                if (response.status == 200) {
                    location.reload();
                }
            },
            error: function (xhr) {
                let errors = xhr.responseJSON.errors;
                let errorMessage = '';
                $.each(errors, function (key, value) {
                    errorMessage += value[0] + '\n';
                });
                alert(errorMessage);
            }
        });
    });

    // Edit section
    $('.edit-section').on('click', function () {
        $('#section_master_id').val($(this).data('id'));
        $('#edit_section_name').val($(this).data('name'));
        $('#edit_service_support_type').val($(this).data('key'));
        $('#edit_lob').val($(this).data('value'));
    });

    // / Save changes for section

    $('#editSectionForm').on('submit', function (e) {
        e.preventDefault(); // Prevent the default form submission
        var id = $('#section_master_id').val();
        var section = $('#edit_section_name').val();
        var sst = $('#edit_service_support_type').val();
        var lob = $('#edit_lob').val();
        const token = $('[name="_token"]').val();

        $.ajax({
            url: 'api/updateSection',
            method: 'PUT',
            data: {
                _token: token,
                id: id,
                section: section,
                sst: sst,
                lob: lob
            },
            success: function (response) {
                // Handle success
                if (response.status === 200) {
                    // Update the corresponding row with new data
                    var row = $('button.edit-section[data-id="' + id + '"]').closest('tr');
                    row.find('td:nth-child(1)').text(lob);
                    row.find('td:nth-child(2)').text(sst);
                    row.find('td:nth-child(3)').text(section);
                    $('#editSectionModal').modal('hide');
                    // Optional: Show a success message
                }
            },
            error: function (xhr) {
                // Handle errors
                alert('Something went wrong!');
            }
        });
    });

    // Delete section
    $('.delete-section').on('click', function () {
        var id = $(this).attr('data-id');

        const token = $('[name="_token"]').val();
        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/deleteSection',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    id: id
                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'X-CSRF-TOKEN': token,
                    'X-Requested-With': 'XMLHttpRequest'
                },
                success: function (response) {
                    // Handle success
                    location.reload(); // Refresh the page to see changes
                },
                error: function (xhr) {
                    // Handle errors
                    alert('Something went wrong!');
                }
            });
        }
    });

    // edit feild
    $('.edit-section-field').on('click', function () {
        $('#field_master_id').val($(this).data('id'));
        $('#field_master_lob').val($(this).data('name'));
        $('#field_master_sst').val($(this).data('key'));
        $('#field_master_section').val($(this).data('value'));
        $('#field_master_field').val($(this).data('feild'));
    });


    // create section feild

    $.ajax({
        url: 'api/lob/list', // Assuming this is the correct URL
        method: 'GET',
        dataType: 'json',
        success: function(response) {
            if(response.status == 200) {
                let lobDropdown = $('#lobDropdown');
                $.each(response.data, function(index, item) {
                    // Append each LOB name as an option
                    var option = '<option value="' + item.lob_name + '">' + item.lob_name + '</option>';
                    lobDropdown.append(option);
                });
            }
        },
        error: function(xhr) {
            console.error("Error fetching LOBs:", xhr);
        }
    });
    $('#submitBtnField').on('click', function (e) {

        $.ajax({
            url: 'api/createField',
            method: 'POST',
            data: $('#fieldForm').serialize(),
            success: function (response) {
                if (response.status == 200) {
                    location.reload();
                }
            },
            error: function (xhr) {
                let errors = xhr.responseJSON.errors;
                let errorMessage = '';
                $.each(errors, function (key, value) {
                    errorMessage += value[0] + '\n';
                });
                alert(errorMessage);
            }
        });
    });

    // Edit sst
    $('.edit-section').on('click', function () {
        var id = $(this).data('id');
        var name = $(this).data('name');

        $('#edit_sst_id').val(id);
        $('#edit_sst_name').val(name);
    });

    // Save changes for Feild
    $('#editfieldForm').on('submit', function (e) {
        e.preventDefault(); // Prevent the default form submission

        var id = $('#field_master_id').val();
        var lob = $('#field_master_lob').val();
        var sst = $('#field_master_sst').val();
        var section = $('#field_master_section').val();
        var field = $('#field_master_field').val();
        const token = $('[name="_token"]').val();

        $.ajax({
            url: 'api/updateField', // Make sure this matches your route
            method: 'PUT',
            data: {
                _token: token,
                id: id,
                lob: lob,
                sst: sst,
                section: section,
                field: field
            },
            success: function (response) {
                if (response.status === 200) {
                    // Update the corresponding row with new data
                    var row = $('button.edit-section-field[data-id="' + id + '"]').closest('tr');
                    row.find('td:nth-child(1)').text(lob);
                    row.find('td:nth-child(2)').text(sst);
                    row.find('td:nth-child(3)').text(section);
                    row.find('td:nth-child(4)').text(field);
                    $('#editfieldModal').modal('hide');
                    // Optional: Show a success message
                } else {
                    alert('Failed to update field.');
                }
            },
            error: function (xhr) {
                // Handle errors
                alert('Something went wrong!');
            }
        });
    });


    // Delete feild
    $('.delete-field').on('click', function () {
        var id = $(this).attr('data-id');
        var token = $('meta[name="csrf-token"]').attr('content');

        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/deleteField',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    id: id
                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'X-CSRF-TOKEN': token,
                    'X-Requested-With': 'XMLHttpRequest'
                },
                success: function (response) {
                    // Handle success
                    location.reload(); // Refresh the page to see changes
                },
                error: function (xhr) {
                    // Handle errors
                    alert('Something went wrong!');
                }
            });
        }
    });




});



