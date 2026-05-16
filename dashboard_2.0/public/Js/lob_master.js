$(function(){
    $(".lobs_list").change(function(){
        $check = $(this).is(":checked")
        if($check)
        {
            var action  = 'add';
        }
        else
        {
            var action = 'remove'
        }
        var token = $("[name='_token']").val();
        $.post("lob/enable",{action:action,lobs:$(this).val(),_token:token},function(data){
            try {
                var data = JSON.parse(data);
                console.log(data);
            } catch (e) {
                toastr.error('Some Error Occured Please Try again After some time again ')
                return false;
            }
            if(data.code==200){
                toastr.success('Lob Master Updated Successfully');
            }
            else if(data.message)
            {
                toastr.error(data.message);
            }
            else if(data.code ==400)
            {
                toastr.error('Some Error Occured Please Try again After some time again ')
                return false;
            }
            else{
                toastr.error('Some Error Occured Please Try again After some time again ')
                return false;
            }

        })


    })

})

$(document).ready(function () {
// create Lob Data
    $('#sstMasterForm').on('submit', function(e) {
        e.preventDefault();

        const token = $("[name='apitoken']").val();

        var formData = new FormData();

        formData.append('_token', token);
        formData.append('lob_name', $('#lob_name').val());
        formData.append('lob', $('#lob').val());
        formData.append('is_enabled', $('#is_enabled').val());
        formData.append('frontend_url', $('#frontend_url').val());
        formData.append('lob_icon', $('#lob_icon')[0].files[0]);
        formData.append('lob_master_name', $('#lob_master_name').val());
        formData.append('customer_frontend_url', $('#customer_frontend_url').val());
        formData.append('payment_url', $('#payment_url').val());

        console.log(formData);

        $.ajax({
            url: 'api/lob/store',
            method: 'POST',
            data: formData,
            processData: false,
            contentType: false,
            headers: {
                'Authorization': 'Bearer ' + token,
                'Accept': 'application/json'
            },
            success: function(response) {
                if (response.status == 200) {
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


    $('.edit-section-field').on('click', function () {
        $('#field_master_id').val($(this).data('id'));
        $('#field_master_lob').val($(this).data('name'));
        $('#field_master_sst').val($(this).data('key'));
        $('#field_master_field').val($(this).data('frontend_url'));
        $('#field_master_name').val($(this).data('lob_master_name'));
        $('#is_enabled').val($(this).data('enabled'));
        
        $('#field_master_field_payment_url').val($(this).data('payment_url'));
        $('#field_master_field_cust_url').val($(this).data('customer_frontend_url'));

        $('#edit_is_enabled').val($(this).data('enabled'));

        $('#field_master_logo').val(''); 
        $('#currentLogoText').text("Current: " + $(this).data('lob_icon'));
    });

    $('#editfieldForm').on('submit', function(e) {
        e.preventDefault();

        let formData = new FormData(this);
        const apitoken = $("[name='apitoken']").val();

        console.log([...formData.entries()]);

        $.ajax({
            url: APP_URL + '/api/updateLobData',
            type: 'POST',
            data: formData,
            contentType: false,
            processData: false,
            headers: {
                'Authorization': 'Bearer ' + apitoken,
                'Accept': 'application/json'
            },
            success: function(response) {
                if (response.status === 200) {
                    $('#editfieldModal').modal('hide');
                    location.reload();
                }
            },
            error: function(xhr) {
                alert('Error: ' + (xhr.responseJSON?.message || 'Unknown error'));
            }
        });
    });

    
});

