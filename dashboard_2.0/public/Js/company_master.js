$(document).ready(function () {
    $('#sstMasterForm').on('submit', function(e) {
        e.preventDefault();
        const token = $("[name='apitoken']").val();


        var formData = new FormData();
        formData.append('_token', token);
        formData.append('lobname', $('#lobname').val());
        formData.append('company_name', $('#company_name').val());
        formData.append('company_shortname', $('#company_shortname').val());
        formData.append('logo', $('#logo')[0].files[0]) ?? '';
        formData.append('live_insu_company', $('#live_insu_company').val());

        console.log(formData);
        $.ajax({
            url: 'api/master_company/store',
            method: 'POST',
            data: formData,
            processData: false,
            contentType: false,
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

    // Delete Company
    $('.delete-sst').on('click', function () {
        var id = $(this).attr('data-id');


        var token = $('meta[name="csrf-token"]').attr('content');
        if (confirm('Are you sure you want to delete this status?')) {
            $.ajax({
                url: 'api/master_company/deleteCompany',
                method: 'POST',
                data: JSON.stringify({
                    _token: token,
                    company_id: id,
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

     // edit feild
     $('.edit-section-field').on('click', function () {
        $('#field_master_id').val($(this).data('id'));
        $('#lobname').val($(this).data('lobname'));
    
        let livelobnameValue = $(this).data('lobname');
        if (livelobnameValue === 'HEALTH' || livelobnameValue === 'MOTOR') {
            $('#lob_name').val(livelobnameValue).trigger('change');
        }
    
        $('#field_master_companyName').val($(this).data('name'));
        $('#field_master_sst').val($(this).data('key'));
        $('#field_master_logo').val(''); 
        $('#field_master_old_logo').val($(this).data('logo')); 
        $('#remove_logo').prop('checked', false); 
    
       
        $('#logoPreviewContainer').hide(); 
    
        
        const logoPath = $(this).data('logo');
        if (logoPath) {
            $('#logoPreview').attr('src', '/storage/' + logoPath); 
            $('#logoPreviewContainer').show(); 
        }
    
        let liveValue = $(this).data('live_insu_company');
        if (liveValue === 'Y' || liveValue === 'N') {
            $('#live_insu_companyflag').val(liveValue).trigger('change');
        }
    }); 


    // Update Company

    $('#editfieldForm').on('submit', function (e) {
        e.preventDefault();
    
        const id = $('#field_master_id').val();
        const lobname = $('#lob_name').val();
        const company_name = $('#field_master_companyName').val();
        const company_shortname = $('#field_master_sst').val();
        const logo = $('#field_master_logo')[0].files[0];
        // const old_logo = $('#field_master_old_logo').val();
        const live_insu_company = $('#live_insu_companyflag').val();
        const remove_logo = $('#remove_logo').is(':checked') ? 1 : 0;
        const token = $('meta[name="csrf-token"]').attr('content'); 
    
        let formData = new FormData();
        formData.append('_token', token);
        formData.append('id', id);
        formData.append('lobname', lobname);
        formData.append('company_name', company_name);
        formData.append('company_shortname', company_shortname);
        formData.append('live_insu_company', live_insu_company);
        formData.append('remove_logo', remove_logo);
    
        if (logo) {
            formData.append('logo', logo);
        } else {
            formData.append('old_logo', old_logo);
        }
    
        $.ajax({
            url: 'api/master_company/updateCompany',
            method: 'POST',
            data: formData,
            processData: false,
            contentType: false,
            success: function (response) {
                if (response.status === 200) {
                    alert(response.message);
                    location.reload();
                } else {
                    alert('Update failed.');
                }
            },
            error: function (xhr) {
                let errors = xhr.responseJSON.errors;
                let errorMessage = '';
                if (errors) {
                    $.each(errors, function (key, value) {
                        errorMessage += value[0] + '\n';
                    });
                    alert(errorMessage);
                } else {
                    alert('Something went wrong!');
                }
            }
        });
    });
    
    


});
