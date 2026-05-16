$(document).ready(function () {
        // create OEM Data
        $('#sstMasterForm').on('submit', function(e) {
            e.preventDefault();

            const token = $("[name='apitoken']").val();

            var formData = new FormData();

            formData.append('_token', token);
            formData.append('oem_name', $('#oem_name').val());


            console.log(formData);

            $.ajax({
                url: 'api/oem_master/store',
                method: 'POST',
                data: formData,
                processData: false,
                contentType: false,
                headers: {
                    'Authorization': 'Bearer ' + token,
                },
                success: function(response) {
                    if (response.status == 200) {
                        // location.reload();
                        $('#misOnboardingSection').show();
                    }
                },
                error: function(xhr) {
                    let errors = xhr.responseJSON.errors;
                    let errorMessage = '';
                    $.each(errors, function(key, value) {
                        errorMessage += value[0] + '\n';
                    });
                    alert(errorMessage);
                }
            });
        });


        // edit OEM Data
         $('.edit-section-field').on('click', function () {
            $('#field_master_id').val($(this).data('id'));
            $('#field_master_lob').val($(this).data('name'));
            $('#field_master_sst').val($(this).data('key'));
            $('#field_master_section').val($(this).data('value'));
            $('#field_master_field').val($(this).data('feild'));
            $('#field_master_url').val($(this).data('url'));
            $('#field_master_logo').val($(this).data('logo'));
            $('#field_master_enabled').val($(this).data('enabled'));
            $('#field_master_disabled').val($(this).data('disabled'));


        });


    // create MISP
        $('#oemMasterForm').on('submit', function(e) {
            e.preventDefault();

            const token = $("[name='apitoken']").val();

            var formData = new FormData();

            formData.append('_token', token);
            formData.append('oem_name', $('#oem_name').val());
            formData.append('misp_name', $('#misp_name').val());
            formData.append('pan_number', $('#pan_number').val());
            formData.append('zone', $('#zone').val());
            formData.append('gstin', $('#gstin').val());
            formData.append('dealer_code', $('#dealer_code').val());



            console.log(formData);

            $.ajax({
                url: 'api/oem_master/store',
                method: 'POST',
                data: formData,
                processData: false,
                contentType: false,
                headers: {
                    'Authorization': 'Bearer ' + token,
                },
                success: function(response) {
                    if (response.status == 200) {
                        // location.reload();
                        $('#branchSection').show();
                    }
                },
                error: function(xhr) {
                    let errors = xhr.responseJSON.errors;
                    let errorMessage = '';
                    $.each(errors, function(key, value) {
                        errorMessage += value[0] + '\n';
                    });
                    alert(errorMessage);
                }
            });
        });


    // create OEM Master

        let recordId = null;

        $('#branchForm').on('submit', function(e) {
            e.preventDefault();

            const token = $("[name='apitoken']").val();
            const submissionStage = $('#submission_stage').val();
            const oemName = $('#oem_name').val();

            var formData = new FormData();

            formData.append('_token', token);
            formData.append('submission_stage', submissionStage);
            formData.append('oem_name', oemName);

            if (recordId) {
                formData.append('id', recordId);
            }

            formData.append('misp_name', $('#misp_name').val());
            formData.append('pan_number', $('#pan_number').val());
            formData.append('zone', $('#zone').val());
            formData.append('gstin', $('#gstin').val());
            formData.append('dealer_code', $('#dealer_code').val());
            formData.append('branch_name', $('#branch_name').val());
            formData.append('address', $('#address').val());
            formData.append('head_office', $('#head_office').val());
            formData.append('misp_code', $('#misp_code').val());
            formData.append('pin_code', $('#pin_code').val());
            formData.append('city', $('#city').val());
            formData.append('state', $('#state').val());
            formData.append('mob_no', $('#mob_no').val());
            formData.append('email', $('#email').val());
            formData.append('status', $('#status').val());

            $.ajax({
                url: 'api/oem_master/storeBranch',
                method: 'POST',
                data: formData,
                processData: false,
                contentType: false,
                headers: {
                    'Authorization': 'Bearer ' + token,
                },
                success: function(response) {
                    if (response.status == 200) {
                        recordId = response.return_data.id;
                        $('#branchSection').show();
                        location.reload();
                    }
                },
                error: function(xhr) {
                    let errors = xhr.responseJSON.errors;
                    let errorMessage = '';
                    $.each(errors, function(key, value) {
                        errorMessage += value[0] + '\n';
                    });
                    alert(errorMessage);
                }
            });
        });


    // Delete OEM Master
        $('.delete-sst').on('click', function () {
            var id = $(this).attr('data-id');
            console.log(id);
            const token = $("[name='apitoken']").val();

            if (confirm('Are you sure you want to delete this status?')) {
                $.ajax({
                    url: 'api/oem_master/delete',
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

    // Get Input feild in Edit Modal
        $('#submitBtn').on('click', function (e) {
            e.preventDefault();

            let oemId = $(this).data('id');
            let oemName = $(this).data('oem-name');
            let mispName = $(this).data('misp-name');
            let panNumber = $(this).data('pan-number');
            let zone = $(this).data('zone');
            let gstin = $(this).data('gstin');
            let dealerCode = $(this).data('dealer-code');

            console.log('OEM ID:', oemId);
            console.log('OEM Name:', oemName);
            console.log('MISP Name:', mispName);
            console.log('PAN Number:', panNumber);
            console.log('Zone:', zone);
            console.log('GSTIN:', gstin);
            console.log('Dealer Code:', dealerCode);
        });

    // Update OEM Master
        $('#updateMispForm').on('submit', function(e) {
            e.preventDefault();

            const token = $("[name='apitoken']").val();
            const mispId = $('#misp_id').val();

            var formData = new FormData();

            formData.append('_token', token);
            formData.append('id', mispId);
            formData.append('misp_name', $('#misp_name').val());
            formData.append('oem_name', $('#oem_name').val());
            formData.append('pan_number', $('#pan_number').val());
            formData.append('zone', $('#zone').val());
            formData.append('gstin', $('#gstin').val());
            formData.append('dealer_code', $('#dealer_code').val());
            formData.append('branch_name', $('#branch_name').val());
            formData.append('address', $('#address').val());
            formData.append('head_office', $('#head_office').val());
            formData.append('misp_code', $('#misp_code').val());
            formData.append('pin_code', $('#pin_code').val());
            formData.append('city', $('#city').val());
            formData.append('state', $('#state').val());
            formData.append('mob_no', $('#mob_no').val());
            formData.append('email', $('#email').val());
            formData.append('status', $('#status').val());


            $.ajax({
                url: 'api/oem_master/updateMisp',
                method: 'POST',
                data: formData,
                processData: false,
                contentType: false,
                headers: {
                    'Authorization': 'Bearer ' + token,
                },
                success: function(response) {
                    if (response.status == 200) {
                        alert(response.message);
                        location.reload();
                    }
                },
                error: function(xhr) {
                    let errors = xhr.responseJSON.errors;
                    let errorMessage = '';
                    $.each(errors, function(key, value) {
                        errorMessage += value[0] + '\n';
                    });
                    alert(errorMessage);
                }
            });
        });


    });
