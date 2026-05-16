function myFunction() {
    document.getElementById("myDropdown").classList.add("show");
}
$(document).ready(function() {

    var editorInstance;


    ClassicEditor
        .create(document.querySelector('#content_id'))
        .then(editor => {
            window.editor = editor;
            editorInstance = editor;
        })
        .catch(error => {
            console.error(error);
        });

    $('#communication_type').change(function() {
        var communicationType = $(this).val();
        $('#email_template, #sms_template, #whatsapp_template').hide();
        if (communicationType === 'email') {
            $('#content_field').show();
            $('#dlt_id').hide();
            $('#communication_email').hide();


            if (!editorInstance) {
                ClassicEditor.create(document.querySelector('#email_content'))
                    .then(editor => {
                        editorInstance = editor;
                    })
                    .catch(error => console.error(error));
            }
        } else if (communicationType === 'sms') {

            $('#content_field').show();
            $('#dlt_id').show();
            $('#email_field').hide();

        } else if (communicationType === 'whatsapp') {

             $('#content_field').show();
            $('#dlt_id').show();

        }
    });


    $('#communication_type').trigger('change');

    setTimeout(function() {
        $('.alert-success').hide();
    }, 1000);

    setTimeout(function () {
        $('#flash-message').alert('close');
    }, 5000);


    // Create Template

        $('#sstMasterForm').on('submit', function (e) {
        e.preventDefault();

        const content = window.editor.getData();
        console.log(content);

        const token = $("[name='apitoken']").val();

        var formData = {
            _token: token,
            title: $('#title').val(),
            communication_type: $('#communication_type').val(),
            event: $('#event').val(),
            content: content,
            status: $('#status').is(':checked') ? 'Y' : 'N'
        };

        $.ajax({
            url: '/api/template_master/store',
            method: 'POST',

            data: JSON.stringify({
                _token: $("[name='apitoken']").val(),
                title: $('#title').val(),
                communication_type: $('#communication_type').val(),
                event: $('#event').val(),
                content: window.editor.getData(),
                status: $('#status').is(':checked') ? 'Y' : 'N'
            }),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'X-CSRF-TOKEN': token,
                'X-Requested-With': 'XMLHttpRequest'
            },
            success: function (response) {
                if (response.status == 200) {

                    window.location.href = '/template';
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

    // Delete Template
    $('.delete-sst').on('click', function () {
        console.log("delete data");
        var id = $(this).attr('data-id');

        const token = $("[name='apitoken']").val();
        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/template_master/deleteTemplate',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    template_id: id,
                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'X-CSRF-TOKEN': token,
                    'X-Requested-With': 'XMLHttpRequest'
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

    // Edit Template
    $('.edit-template').on('click', function () {
        console.log("fsdfdfds");
        var id = $(this).data('id');
        var title = $(this).data('title');
        var communicationType = $(this).data('communication_type');
        var dltId = $(this).data('dlt_id');
        var event = $(this).data('event');
        var content = $(this).data('content');
        var status = $(this).data('status');


        $('#edit_template_id').val(id);
        $('#edit_template_title').val(title);
        $('#edit_template_communication_type').val(communicationType);
        $('#edit_template_dlt_id').val(dltId);
        $('#edit_template_event').val(event);
        $('#content_id').val(content);
        $('#edit_template_status').val(status);


        editorInstance.setData(content);
        // console.log($('#content_id').val(),"content");
    });

    // Update Template
    $('#editStatusForm').on('submit', function (e) {
        e.preventDefault();
        const token = $("[name='apitoken']").val();

        var formData = {
            _token: token,
            id: $('#edit_template_id').val(),
            title: $('#edit_template_title').val(),
            communication_type: $('#edit_template_communication_type').val(),
            dlt_id: $('#edit_template_dlt_id').val(),
            event: $('#edit_template_event').val(),
            content: $('#content_id').val(),
            status: $('#edit_template_status').val(),
        };
        console.log(formData);
        $.ajax({
            url: 'api/template_master/updateTemplate',
            type: 'PUT',
            data: JSON.stringify(formData),
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'X-CSRF-TOKEN': token,
                'X-Requested-With': 'XMLHttpRequest'
            },
            success: function (response) {

                alert('Template updated successfully!');

                $('#editStatusModal').modal('hide');
                location.reload();
            },
            error: function (xhr, status, error) {

                alert('Please fill all the required fields.');
                console.log(xhr.responseText);
            }
        });
    });
});
