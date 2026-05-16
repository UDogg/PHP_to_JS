
$(document).ready(function() {
    // Edit button click
    $('.editbtn').on('click', function() {
        $('#editId').val($(this).data('id'));
        $('#editName').val($(this).data('name'));
        $('#editKey').val($(this).data('key'));
        $('#editValue').val($(this).data('value'));
        $('#editModal').modal('show');
    });

    // Update data
    $('#editForm').on('submit', function(e) {
        e.preventDefault();
        const token = $('[name="_token"]').val();
        let id = $('#editId').val();
        let name = $('#editName').val();
        let key = $('#editKey').val();
        let value = $('#editValue').val();

        $.ajax({
            url: APP_URL + '/PolicyStatusFilterMaster/update', 
            method: 'POST',
            data: {
                _token: token,
                id: id,
                name: name,
                key: key,
                value: value
            },
            success: function(response) {
                location.reload();
            }
        });
    });

    // Delete button click
    $('.deletebtn').on('click', function() {
        const token = $('[name="_token"]').val();
        let id = $(this).data('id');
    
        if (confirm('Are you sure you want to delete this data?')) {
            $.ajax({
                url: APP_URL + '/PolicyStatusFilterMaster_delete/' + id, 
                method: 'DELETE',  
                data: {
                    _token: token,
                    _method: 'DELETE'  
                },
                success: function(response) {
                    alert(response.success);
                     location.reload();
                },
                error: function(xhr) {
                    console.log(xhr.responseText);
                    alert('Something went wrong');
                }
            });
        }
    });
    
});

$(function(){
    $(".col_div").hide();
    $(".stage_div").hide()
    $("#LobID").select2({closeOnSelect: false})

    $("#LobID").on('select2:select select2:unselect',function(){
        const lob = $(this).val();
        const _token = $("[name='_token']").val();
        $.post('GetColumns',{lob:lob,_token:_token},function(data){
            const columns = $("[name='columns']");
            columns.empty();
            columns.append("<option value=''>Select Column</option>")
            $.each(data.data,function(key,val){
                columns.append("<option value='"+val.id+"'>"+val.column_name+"</option>")
            })
        })
    })

    $(".add_pair").click(function(){
            const filter_name = $("[name='filter_name']");
            const stage = $("[name='stage']");
            const lob = $("[name='lob[]']");
            const columns = $("[name='columns']");
            const key = $("[name='key']");
            const value = $("[name='value']");
            const filytr_type = $("[name='filter_type']");
            if(filter_name.val()=='')
            {
                toastr.warning('Please Enter Filter Name')
                return false
            }
            if(filytr_type.val() == '')
            {
                toastr.warning('Please Select Filter Type')
                return false
            }
            if(filytr_type.val() == 1)
            {
                if(stage.val()=='')
                {
                    toastr.warning('Please Select Stage')
                    return false
                }
                if(lob.val() == '')
                {
                    toastr.warning('Please Select Lob')
                    return false
                }
            }
            else if(filytr_type.val() == 2)
            {
                if(lob.val() == '')
                {
                    alert("fefsefsefseff");
                    toastr.warning('Please Select Lob')
                    return false
                }
                if(columns.val() == '')
                {
                    toastr.warning('Please Select Column')
                    return false
                }
                if(key.val() == '')
                {
                    toastr.warning('Please Enter Key')
                    return false
                }
                if(value.val() == '')
                {
                    toastr.warning('Please Enter Value')
                    return false
                }
            }
        const forn_data = $("[name='filter_master']").serialize();
        $.ajax({
            url: APP_URL +'/PolicyStatusFilterMaster',
            method:'POST',
            data:forn_data,
            success:function(data){

                if(data.status == 200)
                {
                    toastr.success('Filter Added Successfully')
                   $("[name='key']").val('')
                   $("[name='value']").val('')
                }
                else if(data.status == 503)
                {
                    toastr.error(data.error)
                }
                else
                {
                    toastr.error("some error occured please try again after some time")
                }
            }, error: function(xhr, status, error) {
                console.error(" AJAX Error:", error);
                console.log("Status:", status);
                console.log("Response Text:", xhr.responseText);
            }
        })
    })
    $("[name='filter_type']").change(function(){
        const filter_val = $(this).val();
        if(filter_val == '1')
        {
            $(".stage_div").show();
            $(".col_div").hide();
        }
        else if(filter_val == '2')
        {
            $(".col_div").show();
            $(".stage_div").hide();
            $(".select2").select2({
                closeOnSelect: false
            })
        }
        else
        {
            $(".stage_div").hide();
            $(".col_div").hide();
        }

    })
})
