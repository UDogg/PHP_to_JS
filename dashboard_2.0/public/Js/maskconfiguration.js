$(document).ready(function () {
    $('#submitBtnSst').on('click', function (e) {
        var key_name = $('#key_name').val();
        var masking_position = $('#masking_position').val();
        var masking_symbol = $('#masking_symbol').val();
        var token = $("[name='_token']").val();
        console.log(token);
        var formData = {
            key_name: key_name,
            masking_position: masking_position,
            masking_symbol: masking_symbol,
        };
        $.ajax({
            url: 'api/maskconfiguration/add',
            method: 'POST',
            data: JSON.stringify(formData),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'X-CSRF-TOKEN': token
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

    // Delete Company
    $('.delete-sst').on('click', function () {
        var id = $(this).attr('data-id');
        // console.log(id);

        var token = $('meta[name="csrf-token"]').attr('content');
        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/maskconfiguration/delete',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    id: id,
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
        $('#field_master_url').val($(this).data('url'));
        $('#field_master_logo').val($(this).data('logo'));
        $('#field_master_is_renewal').val($(this).data('is_renewal'));
        $('#field_master_is_renewal_bike').val($(this).data('is_renewal_bike'));
    });


    $('#editfieldForm').on('submit', function (e) {
        e.preventDefault(); // Prevent the default form submission

        var id = $('#field_master_id').val();
        var lob = $('#field_master_lob').val();
        var sst = $('#field_master_sst').val();
        var section = $('#field_master_section').val();
        var field = $('#field_master_field').val();
        var url = $('#field_master_url').val();
        var logo = $('#field_master_logo').val();
        var is_renewal = $('#field_master_is_renewal').val();
        var is_renewal_bike = $('#field_master_is_renewal_bike').val();

        const token = $('[name="_token"]').val();

        $.ajax({
            url: 'api/master_company/updateCompany', // Make sure this matches your route
            method: 'PUT',
            data: {
                _token: token,
                id: id,
                lob: lob,
                sst: sst,
                section: section,
                field: field,
                url: url,
                logo: logo,
                is_renewal: is_renewal,
                is_renewal_bike: is_renewal_bike


            },
            success: function (response) {
                if (response.status === 200) {
                    // Update the corresponding row with new data
                    var row = $('button.edit-section-field[data-id="' + id + '"]').closest('tr');
                    row.find('td:nth-child(1)').text(lob);
                    row.find('td:nth-child(2)').text(sst);
                    row.find('td:nth-child(3)').text(section);
                    row.find('td:nth-child(4)').text(field);
                    row.find('td:nth-child(5)').text(url);
                    row.find('td:nth-child(6)').text(logo);
                    row.find('td:nth-child(7)').text(is_renewal);
                    row.find('td:nth-child(8)').text(is_renewal_bike);
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

});
