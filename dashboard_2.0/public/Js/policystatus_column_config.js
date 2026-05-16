$(document).ready(function() {
    // Ensure Select2 initializes properly
    $('.select2').select2({
        placeholder: "Select options",
        allowClear: true,
        width: '100%',
        closeOnSelect: false
    });

    // Handle default column selection
    $(".is_def").click(function() {
        var element = $(this);
        var def_val = element.attr('is_default') === 'Y' ? 'N' : 'Y'; 
        var column_name = element.attr('column_name'); 
        var lob_sel = $("#lob_sel").val(); 
        var stage_sel = $("#sel_stage").val();
        var token = $("[name='_token']").val();

        if (!lob_sel || lob_sel.length === 0) {
            toastr.error("Please select at least one LOB.");
            return;
        }

        var requestData = {
            _token: token,
            column_name: column_name,
            is_default: def_val,
            lob_sel: lob_sel,
            stage_sel: stage_sel
        };

        $.ajax({
            url: 'DefaultColumns',
            type: 'POST',
            data: requestData,
            dataType: 'json',
            success: function(response) {
                if (response.status === 'true') {
                    toastr.success('Column Updated Successfully');

                    // Update UI
                    $(".is_def").each(function() {
                        var item = $(this);
                        if (item.attr("column_name") === column_name) {
                            item.attr("is_default", "N");
                            item.css("background-color", "white");
                        }
                    });

                    element.attr('is_default', def_val);
                    element.css('background-color', def_val === 'Y' ? 'black' : 'white');
                } else {
                    toastr.error('Failed to update column.');
                }
            },
            error: function(xhr) {
                console.error("🔴 AJAX Error:", xhr.responseText);
                toastr.error("Request failed. Check console for details.");
            }
        });
    });

    // Alias edit handler
    $(".alias_ed").click(function(){
        var name = $(this).attr('ed_val');
        var id = $(this).attr('ed_id');
        var token = $("[name='_token']").val();
        $("#modal-default").modal('show');
        var new_val = $(this).attr('new_val');
        if(new_val != '')
        {
            $("#alias_name").val(new_val);
        }
        var order_val = $(this).attr('order_val');
        //Prefill order_by 
        $("#order_by_input").val(order_val || '');

        // Unbind previous click events to prevent duplicate bindings
        $(".sb_clmn_up").off('click').on('click', function(){
            var alias = $('#alias_name').val();
            var order = $('#order_by_input').val();
            $.post('update_column_master', {column_id: id, column_name: name, _token: token, alias: alias, order_by: order}, function(response){

                try {
                    var data = JSON.parse(response);
                    console.log(data);
                } catch (e) {
                    toastr.error('Some Error Occured Please Try again After some time again ')
                    return false;
                }

                if(data.status == 'true'){
                    $("#modal-default").modal('hide');
                    toastr.success('Column Updated Successfully')
                    location.reload();
                } else if(data.message !== ''){
                    toastr.error(data.message)
                    return false;
                } else{
                    toastr.error('Some Error Occured Please Try again After some time again ')
                    $("#modal-default").modal('hide');
                    location.reload();
                    return false;
                }
            });
        });
    });

    // Restore Select2 on dynamically loaded elements
    $(document).ajaxComplete(function() {
        $('.select2').select2({
            placeholder: "Select options",
            allowClear: true,
            width: '100%'
        });
    });
});
