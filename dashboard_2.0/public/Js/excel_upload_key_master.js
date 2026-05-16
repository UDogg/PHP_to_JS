$(function(){

    $(".alias_ed").click(function(){
        var name = $(this).attr('ed_val');
        var id = $(this).attr('ed_id');
        var token = $("[name='_token']").val();
        var new_val = $(this).attr('new_val');
        $("#modal-default").modal('show');
        if(new_val !== '') {
            $("#alias_name").val(new_val);
        }
        $(".sb_clmn_up").one('click', function(){
            var alias = $('#alias_name').val();
    
            $.ajax({
                url: 'http://127.0.0.1:8000/excel-upload/UpdateColumnNameToExcel',
                type: 'POST',
                contentType: 'application/json; charset=UTF-8',
                dataType: 'json',
                headers: {
                    'X-CSRF-TOKEN': token,
                    'X-Requested-With': 'XMLHttpRequest'
                },
                data: JSON.stringify({
                    column_id: id,
                    column_name: name,
                    alias: alias
                }),
                success: function(response) {
                    try {
                        var data = response;
                        console.log(data);
                    } catch (e) {
                        toastr.error('Some Error Occurred. Please Try Again Later.');
                        return false;
                    }
    
                    if (data.status === 'true') {
                        $("#modal-default").modal('hide');
                        toastr.success('Column Updated Successfully');
                        location.reload();
                    } else if (data.message !== '') {
                        toastr.error(data.message);
                        return false;
                    } else {
                        location.reload();
                        toastr.error('Some Error Occurred. Please Try Again Later.');
                        $("#modal-default").modal('hide');
                        return false;
                    }
                },
                error: function(xhr, status, error) {
                    toastr.error('Request failed: ' + error);
                }
            });
        });
    });

    $("[name='col_names[]']").change(function() {
        var action = $(this).is(':checked') ? 'add' : 'remove';
        var lob_sel = $("[name='lob_sel']").val();
        var stage_val = $("[name='sel_stage']").val();
        var column_id = $(this).val();
        var token = $("[name='_token']").val();
    
        if (lob_sel == '') {
            toastr.error('Please Select Line of Business');
            $(this).prop('checked', false);
            return false;
        }
    
        if (stage_val == '') {
            toastr.error('Please select the stage also');
            $(this).prop('checked', false);
            return false;
        }
    
        $.ajax({
            url: 'AddColumnToExcel',
            method: 'POST',
            headers: {
             
                'Content-Type': 'application/json; charset=UTF-8',
                'X-Requested-With': 'XMLHttpRequest',
                'X-CSRF-TOKEN': token,
              
             
            },
            data: JSON.stringify({
                col_names: column_id,
                lob_sel: lob_sel,
                action: action,
            }),
            success: function(response) {
                try {
                    if (response.status == 'true') {
                        if (action === 'add') {
                            toastr.success(response.message || 'Column Inserted Successfully');
                        } else {
                            toastr.success(response.message || 'Column Removed Successfully');
                        }
                    } else {
                        toastr.error(response.message || 'Some Error Occurred. Please Try Again After Some Time.');
                        return false;
                    }
                } catch (e) {
                    toastr.error('Some Error Occurred. Please Try Again After Some Time.');
                    return false;
                }
            },
            error: function(xhr, status, error) {
                toastr.error('Request failed: ' + error);
                return false;
            }
        });
    });
    $("[name='search_col']").change(function(){
        var search_str = $(this).val();
        if(search_str == '')
        {
            $(".col-sm-6").css('display','block')
        }
        $.each($(".colnms"),function(){
            if(!$(this).text().includes(search_str))
            {
                $(this).closest('.col-sm-6').css('display','none');
            }
        })
    })
})