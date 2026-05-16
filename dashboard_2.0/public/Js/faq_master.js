$(document).ready(function () {
    $('#sstMasterForm').on('submit', function (e) {
        e.preventDefault();

        const token = $("[name='apitoken']").val();
        console.log(token);
        var formData = {
            _token: token,
            tag: $('#tag').val(),
            question: $('#question').val(),
            answer: $('#answer').val(),

        };

        $.ajax({
            url: 'api/faq/store',
            method: 'POST',

            data: JSON.stringify({
                _token: $("[name='apitoken']").val(),
                tag: $('#tag').val(),
                question: $('#question').val(),
                answer: $('#answer').val(),

            }),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'Authorization': 'Bearer ' + token,
            },
            success: function (response) {
                if (response.status == 200) {

                    location.reload();
                } else {
                    alert('Failed to create status.');
                }
            },
            error: function (xhr) {

                let errors = xhr.responseJSON.errors;
                let errorMessage = 'Please fill all the required fields.';
                $.each(errors, function (key, value) {
                    errorMessage += value[0] + '\n';
                });
                alert(errorMessage);
            }



        });
    });

    $('.delete-sst').on('click', function () {
        var id = $(this).attr('data-id');
        console.log(id);
        const token = $("[name='apitoken']").val();

        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: '/api/faq/deleteFaq',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    id: id,
                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers:{
                    'Authorization': 'Bearer ' + token
                },
                success: function (response) {

                    location.reload();
                },
                error: function (xhr) {

                    alert('Something went wrong!');
                }
            });
        }
    });


    $('.edit-section-field').on('click', function () {
        $('#field_master_id').val($(this).data('id'));
        $('#field_master_lob').val($(this).data('name'));
        $('#field_master_sst').val($(this).data('key'));
        $('#field_master_section').val($(this).data('value'));

    });

    // Update Company

    $('#editfieldForm').on('submit', function (e) {
        e.preventDefault();

        var id = $('#field_master_id').val();
        var tag = $('#field_master_lob').val();
        var question = $('#field_master_sst').val();
        var answer = $('#field_master_section').val();


        const token = $("[name='apitoken']").val();


        $.ajax({
            url: 'api/faq/updateFaq',
            method: 'PUT',

            data: JSON.stringify({
                _token: token,
                id: id,
                tag: tag,
                question: question,
                answer: answer,

            }),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'Authorization': 'Bearer ' + token,
            },

            success: function (response) {
                if (response.status == 200) {
                    location.reload();
                } else {
                    alert('Failed to update field.');
                }
            },
            error: function (xhr) {
                alert('Something went wrong!');
            }
        });
    });


});
