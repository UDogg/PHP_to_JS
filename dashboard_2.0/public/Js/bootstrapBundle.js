
    $(document).ready(function () {

    // Create CTA
        $('#sstMasterForm').on('submit', function (e) {
            e.preventDefault();

            const token = $("[name='apitoken']").val();
            var formData = {
                _token: token,
                lobMasterData: $('#lobMasterData').val(),
                stageMasterData: $('#stageMasterData').val(),
                ctaName: $('#ctaNameSelect').val(),
                redirection_url: $('#redirection_url').val() ? $('#redirection_url').val() : null,
            };

            $.ajax({
                url: APP_URL+'/api/cta_master/storeCta',
                method: 'POST',
                data: JSON.stringify(formData),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'Authorization': 'Bearer ' + token,
                },
                success: function (response) {
                    if (response.status == 200) {
                        let cta = response.return_data;
                        let newRow = `<tr>
                                        <td>${cta.lob_name}</td>
                                        <td>${cta.stage_name}</td>
                                        <td>${cta.cta_name}</td>
                                        <td>${cta.redirection_url || ''}</td>
                                        <td>
                                            <button class="btn btn-sm btn-primary edit-section-field"
                                                data-id="${cta.id}"
                                                data-name="${cta.lob}"
                                                data-key="${cta.stage}"
                                                data-value="${cta.cta_name}"
                                                data-url="${cta.redirection_url}"
                                                data-toggle="modal"
                                                data-target="#editFieldModal">
                                                Edit
                                            </button>
                                            <button class="btn btn-sm btn-danger" data-id="${cta.id}" id="delete-sst">
                                                Delete
                                            </button>
                                        </td>
                                    </tr>`;
                        content = sanitizeHtml(newRow);
                        $('table tbody').prepend(content);

                        $('#addModal').modal('hide');
                        // location.reload();
                    } else {
                        alert('Failed to create CTA.');
                    }
                },

                error: function (xhr) {
                    let errors = xhr.responseJSON.errors;
                    let errorMessage = 'Please fill all the required fields.\n';
                    $.each(errors, function (key, value) {
                        errorMessage += value[0] + '\n';
                    });
                    alert(errorMessage);
                }
            });
        });


    // Delete CTA
        $('#delete-sst').on('click', function () {
            console.log("1")
            var id = $(this).attr('data-id');

            const token = $("[name='apitoken']").val();

            if (confirm('Are you sure you want to delete this CTA?')) {
                $.ajax({
                    url: APP_URL+'/api/cta_master/delete',
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

    // Edit CTA

        $(document).on('click', '.edit-section-field', function() {

            var id = $(this).data('id');
            var lob = $(this).data('name');
            var stage = $(this).data('key');
            var ctaName = $(this).data('value');
            var redirectionUrl = $(this).data('url');


            $('#cta_id').val(id);
            $('#editLobMasterData').val(lob).trigger('change');
            $('#editStageMasterData').val(stage).trigger('change');
            $('#editCtaName').val(ctaName).trigger('change');
            $('#editRedirectionUrl').val(redirectionUrl);


            $('#editFieldModal').modal('show');
        });

    // Update CTA
        $('#editCtaForm').on('submit', function(e) {
            e.preventDefault();

            var id = $('#cta_id').val();
            console.log(id)
            var Lob = $('#editLobMasterData').val();
            var stage = $('#editStageMasterData').val();
            var cta = $('#editCtaName').val();
            var redirectionUrl = $('#editRedirectionUrl').val();


            const token = $("[name='apitoken']").val();


            $.ajax({
                url: APP_URL+'/api/cta_master/update',
                method: 'PUT',
                data: JSON.stringify({
                    _token: token,
                    id: id,
                    Lob: Lob,
                    stage: stage,
                    cta: cta,
                    redirectionUrl: redirectionUrl

                }),
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'Authorization': 'Bearer ' + token,
                },
                success: function(response) {
                    alert(response.message);
                    $('#editFieldModal').modal('hide');
                    location.reload();
                },
                error: function(xhr) {
                    alert('Something went wrong while updating the CTA!');
                }
            });
        });

    // Filter Lob wise CTA
            $('#lob-filter').on('change', function() {
                const selectedLob = $(this).val();
                const token = $("[name='apitoken']").val()

                $.ajax({
                    url: APP_URL+'/api/cta_master/filter',
                    method: 'GET',
                    headers: {
                        'Authorization': 'Bearer ' + token
                    },
                    data: {
                        lob: selectedLob,
                        token: token
                    },
                    success: function(response) {

                        const tableBody = $('#cta-table-body tbody');
                        tableBody.empty();

                        if (response.cta.length > 0) {
                            response.cta.forEach(cta => {
                                let newRow = `<tr>
                                                <td>${cta.lob}</td>
                                                <td>${cta.stage}</td>
                                                <td>${cta.cta_name}</td>
                                                <td>${cta.redirection_url || ''}</td>
                                                <td>
                                                    <button class="btn btn-sm btn-primary edit-section-field"
                                                        data-id="${cta.id}"
                                                        data-name="${cta.lob_id}"
                                                        data-key="${cta.stage_id}"
                                                        data-value="${cta.cta_id}"
                                                        data-url="${cta.redirection_url}"
                                                        data-toggle="modal"
                                                        data-target="#editFieldModal">
                                                        Edit
                                                    </button>
                                                    <button class="btn btn-sm btn-danger" data-id="${cta.id}" id="delete-sst">
                                                        Delete
                                                    </button>
                                                </td>
                                            </tr>`;
                                tableBody.append(newRow);
                            });
                        } else {
                            tableBody.append('<tr><td colspan="5" class="text-center">No data available.</td></tr>');
                        }
                    },
                    error: function(xhr) {
                        console.error('Failed to load data.');
                    }
                });
            });

            $('#ctaName').select2({
                placeholder: "Select CTA Name",
                allowClear: true
            });



    });

