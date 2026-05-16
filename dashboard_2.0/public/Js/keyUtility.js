$(function(){
    $('.select2').select2({
        closeOnSelect: false
    })


    $(".submit_btn").click(function()
    {
        var updt_check = $("[name='update_mode']").val()
        if(updt_check != '')
        {
            return false;
        }
        var form_data = $('[name="key_utility_frm"]').serialize();
        $.post("KeyUtility",form_data,function(data){

            if(data.status == 200)
            {
                toastr.success('Key Created Successfully')
                setTimeout(function(){
                    location.reload()
                },1500)
            }
            else if(data.status == 503)
            {
                toastr.error(data.error)
            }
            else
            {
                toastr.error('Error In Creating The Key Please Try Again After Some Time')
                setTimeout(function(){
                    location.reload()
                },1500)
            }
        })
    })
    $(".del_img").click(function(){
        var current = $(this);
        var id = $(this).attr("del_id");
        var token = $("[name='_token']").val();
        $ajax = $.ajax({
            url: "KeyUtility/"+id,
            type: "DELETE",
            data: {
                _token: token
            },
            success: function (data) {
                if(data.status == 200){
                    var buton_rm = current.closest(".col-sm-3").hide()
                    console.log(buton_rm)
                    toastr.success('column Deleted Successfully');
                    // location.reload();
                }
            }
        })
    })
    $(".updt_icn").click(function()
    {
        var edit_id = $(this).attr('val_id');
        $("[name='update_mode']").val(edit_id)
        $("[name='key_name']").val($(this).closest("b").text().trim())
        $(".submit_btn").click(function()
        {
            var data = $("[name='key_utility_frm']").serialize();
            $.ajax('KeyUtility/'+edit_id, {
                method: 'PUT',
                data: data,
                success: function (data) {
                    if (data.status == 200) {
                        toastr.success('Key and columns are  Updated Successfully')

                    } else {
                        toastr.error('Error In Updating The Key Please Try Again After Some Time')
                    }
                }
            })
        })
    })
    $(".del_icn").click(function(){
        var current = $(this);
        var del_id = $(this).attr('val_id');
        $("#del_mdl").modal('show');
        $(".del_cnf").click(function(){
            $.ajax('KeyUtility/'+del_id, {
                method: 'DELETE',
                data : {
                    _token: $("[name='_token']").val(),
                    mode: "key"
                },
                success: function (data) {
                    if (data.status == 200) {
                        toastr.success('Key and columns all Deleted Successfully')
                        current.closest(".card").remove()
                        $("#del_mdl").modal('hide');

                    } else {
                        toastr.error('Error In Deleting The Key Please Try Again After Some Time')

                    }
                }
            })
        })
    })

$('.updt_icn').on('click', function () {
    let keyId = $(this).attr('val_id');

    $.ajax({
        url: `/key-utility/${keyId}/edit`, // Fetch the details for the given key
        method: 'GET',
        success: function (response) {
            // Populate the key name and update mode
            $('input[name="key_name"]').val(response.key_name);
            $('input[name="update_mode"]').val(response.key_id);

            // Reset all select fields
            $('select[name^="columns"]').each(function () {
                $(this).val('').trigger('change');
            });

            // Highlight selected options based on response mappings
            response.mappings.forEach(function (mapping) {
                // let selectField = $(`select[name="columns${mapping.lob}[]"]`); // Target the correct LOB select field
                let lob = String(mapping.lob).replace(/[^a-zA-Z0-9_-]/g, '');
                let selectField = $(`select[name="columns${lob}[]"]`);
                
                let currentValues = selectField.val() || []; // Get the current selected values
                currentValues.push(mapping.mapping_id); // Add the mapping_id to the selected values
                selectField.val(currentValues).trigger('change'); // Highlight the selected values
            });

            // Scroll to the form
            $('html, body').animate({
                scrollTop: $("form[name='key_utility_frm']").offset().top
            }, 500);
        },
        error: function () {
            alert('Failed to fetch data for editing.');
        }
    });
});


// Clear form on cancel
$('.cancel_edit').on('click', function () {
    $('input[name="key_name"]').val('');
    $('input[name="update_mode"]').val('');
    $('select[name^="columns"]').each(function () {
        $(this).val('').trigger('change');
    });
});

})

