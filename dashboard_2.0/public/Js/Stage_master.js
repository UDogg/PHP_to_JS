$(document).ready(function() {
    $(".if_add").hide();
  $(".sbt").click(function (){
      // for sub stage creation
      var sub_stage_val = $('[name="sub_stage_name"]').val();
      var stage_val = $('[name="stage_mstr"]').val();
      if(sub_stage_val == "")
      {
          toastr.warning('Please Enter Sub Stage Name')
          $('[name="sub_stage_name"]').focus();
          return false
      }
      if(stage_val == "")
      {
          toastr.warning('Please Select Stage')
          $('[name="stage_mstr"]').focus();
          return false
      }
      var token = $('[name="csrf-token"]').val()
      $.post('sub_stage',$('[name="sub_stage_master"]').serialize(),function(data){
          if(data.message)
          {
              toastr.error(data.message)
              setTimeout(function(){
                location.reload()
              },1200)
              return false
          }
          console.log(data)
        if(data.code == 200)
          {
            toastr.success('Sub Stage Added Successfully')
              setTimeout(function(){
                location.reload()
              },1200)
          }
          else if(data.code == 503)
            {
                toastr.error(data.error);
            }
          else
          {
            toastr.error('Some Error Occured Please Try again After some time again ');
            setTimeout(function(){
              location.reload()
            },1200)
          }
      })

  })
// for stage creation
  $(".c_stage").click(function (){

      var stage_val = $('[name="stage_name"]').val()
      if(stage_val == "")
      {
          toastr.warning('Please Enter Stage Name')
          $('[name="stage_name"]').focus();
          return false
      }
      var token = $('[name="csrf-token"]').val()
    $.post('stagemaster',$('[name="stage_master"]').serialize(),function(data){
      data = JSON.parse(data)
      if(data.code == 200)
        {
          toastr.success('Stage Added Successfully')
            setTimeout(function(){
              location.reload()
            },1000)
        }
        else
        {
          toastr.error(data.error);
          setTimeout(function(){
            location.reload()
          },1000)
        }

    })
    // toastr.success('')
  })

    // for edit of sub stages
    $(".sb_st_btn").on('click',function(){
        var sub_stage_val_edit = $(this).text();
        var stage_id = $(this).attr('p_st_id');
        var sub_stage_id = $(this).attr('p_sub_st_id');
        $("[name='mdl_sb_stg']").val(sub_stage_val_edit);
        $("[name='mdl_sb_stg_old']").val(sub_stage_val_edit);
        $("[name='mdl_stg_id']").val(stage_id);
        $("[name='mdl_sub_stg_id']").val(sub_stage_id);
        $("#modal-default").modal('show');
        $(".cls_mdl").click(function(){
        // $.post('edit_sub_stage', $('[name="mdl_stage_frm"]').serialize(), function(data) {
        //     try {
        //         data = JSON.parse(data)
        //     }
        //     catch (e) {
        //         toastr.error('Error In Updating The Sub Stage Please Try Again After Some Time')
        //         setTimeout(function(){
        //             location.reload()
        //         },1500)
        //         return false
        //     }
        //     if(data.code == 200)
        //     {
        //         toastr.success('Sub Stage Updated Successfully')
        //         setTimeout(function(){
        //             location.reload()
        //         },1500)
        //     }
        //     else
        //     {
        //         toastr.error('Error In Updating The Sub Stage Please Try Again After Some Time')
        //         setTimeout(function(){
        //             location.reload()
        //         },1500)
        //     }
        //
        // })
        $("#modal-default").modal('hide');
        })
    })

        // for sub stage deletion
    $(".del_sub_stage").click(function(){
        $.post('del_sub_stage',$('[name="mdl_stage_frm"]').serialize(),function(data){

            if(data.code == 200)
            {
                toastr.success('Sub Stage Deleted Successfully')
                setTimeout(function(){
                    location.reload()
                },1500)
            }
            else if(data.code == 503)
            {
                toastr.error(data.error)
            }
            else
            {
                toastr.error('Error In Deleting The Sub Stage Please Try Again After Some Time')
                setTimeout(function(){
                    location.reload()
                },1500)
            }
        })

    })


    // delete stage

    $(".deletebtn").click(function(){
        var del_stage_id = $(this).attr('stage_del_id');
        $("#del_stage_mdl").modal('show');
        $('[name="del_stg_id"]').val(del_stage_id);
        $(".del_stage").click(function(){

            var formdata = $('[name="stage_del_frm"]').serialize();
            $.ajax({
                url: "stagemaster/"+del_stage_id,
                type: 'DELETE',
                data: formdata,
                success: function(response) {
                    try {
                        response = JSON.parse(response)
                    }
                    catch (e) {
                        toastr.error('Error In Deleting The Stage Please Try Again After Some Time')
                        setTimeout(function(){
                            location.reload()
                        },1500)
                        return false
                    }
                    if (response.code == 200) {
                        toastr.success('Stage Deleted Successfully')
                        setTimeout(function(){
                            location.reload()
                        },1500)
                    }
                    else
                    {
                        toastr.error('Error In Deleting The Stage Please Try Again After Some Time')
                        setTimeout(function(){
                            location.reload()
                        },1500)
                    }

                },
                error: function(xhr) {
                    console.error(xhr.responseText);
                    // Handle the error
                }
            });
        })

    })


    // for edit of stage master
    $(".edit_stage").click(function()
    {
        var edit_stage_val = $(this).text().trim();
        var stg_id = $(this).attr('stg_id');
        $("#edt_stage_mdl").modal('show');
        $('[name="edt_stage"]').val(edit_stage_val);
        $('[name="edt_stage_id"]').val(stg_id);
        $(".edt_stage").click(function(){
        var form_data = $('[name="ed_stage_frm"]').serialize();

            $.ajax({
                url: "stagemaster/"+stg_id,
                type: 'PUT',
                data: form_data,
                success: function(response) {

                    if (response.code == 200) {
                        toastr.success('Stage Deleted Successfully')
                        setTimeout(function(){
                            location.reload()
                        },1500)
                    }
                    else if(response.code == 503)
                    {
                        toastr.error(data.error)
                        setTimeout(function(){
                            location.reload()
                        },1500)
                    }
                    else
                    {
                        toastr.error('Error In Deleting The Stage Please Try Again After Some Time')
                    }

                },
                error: function(xhr) {
                    console.error(xhr.responseText);
                    // Handle the error
                }
            });
        })


    })

    // add new sub stage
    $(".show_add").click(function(){
        $(".if_add").show('slow');

    })
    $(".sub_new_stage").click(function(){
        var new_substage_val = $("[name='new_sub_stage_name']").val()

        if(new_substage_val == '')
        {
            toastr.error('Please Enter Sub Stage Name')
            return false
        }
        var token = $('[name="_token"]').val();
        $.post('sub_stage',{new_substage_val:new_substage_val,_token:token , action:'new'},function(data){
            if(data.code == 200)
            {
                toastr.success('Sub Stage Added Successfully')
                setTimeout(function(){
                    location.reload()
                },1500)
            }
            else if(data.code == 503)
            {
                toastr.error('Error In Adding The Sub Stage Please Try Again After Some Time')
                setTimeout(function(){
                    location.reload()
                },1500)
            }
            else
            {
                toastr.error('Error In Adding The Sub Stage Please Try Again After Some Time')
                setTimeout(function(){
                    location.reload()
                },1500)
            }

        })
    })

    // set priority for satge master
    $("[name='stage_priority']").change(function(){
        var new_priority = $(this).val();
        var old_priority = $(this).attr('old_val');
        if(old_priority == '')
        {
            old_priority = 0
        }
        const token = $('[name="_token"]').val();
        var stage_id = $(this).attr('stg_id');
        $.post('UpdateStagePriority',{new_priority:new_priority,_token:token ,stage_id:stage_id,old_priority:old_priority},function(data){
            if(data.code == 200)
            {
                toastr.success('Priority Set Successfully')
                setTimeout(function(){
                    location.reload()
                },1500)

            }
            else if(data.code == 503)
            {
                toastr.error(data.error)
                setTimeout(function(){
                    location.reload()
                },1500)
                return  false;
            }
            else
            {
                try {

                data = JSON.parse(data)
                }
                catch (e) {
                    toastr.error('Error In Setting The Priority Please Try Again After Some Time')
                    return false;
                }
                if(data.message != '')
                {
                    toastr.error(data.message)
                    return false;
                }
                else {

                toastr.error('Error In Setting The Priority Please Try Again After Some Time')
                return false;
                }

            }
        })

    })
    $(".renewalstg").click(function(){
        $("#renewal_substage").modal('show');
        $(".add_renewal_stg").click(function(){
            var renewal_substage_val = $("[name='sub_stage_name_renewal[]']").val()
            if(renewal_substage_val == '')
            {
                toastr.error('Please Enter Sub Stage Name')
                return false;
            }
            var token = $('[name="_token"]').val();
            $.post('StageRenewal',{renewal_substage_val:renewal_substage_val,_token:token },function(data){
                if(data.code == 200)
                {
                    toastr.success('Sub Stage Added Successfully For Renewal')
                    $("#renewal_substage").modal('hide');

                }
                else if(data.code == 503)
                {
                    toastr.error(data.error)

                }
                else
                {
                    toastr.error('Error In Adding The Sub Stage Please Try Again After Some Time')
                }
            })

        })

        $("[name='sub_stage_name_renewal[]']").select2({
            closeOnSelect: false
        })
    });

    $(".sel_rene_stg").click(function(){
        const current = $(this);
        const val = current.map(function() {
            return $(this).attr('id');
        }).get();

        const token = $('[name="_token"]').val();
        const action =  'remove';
        $.post('StageRenewal',{renewal_substage_val:val,_token:token,action:action},function(data){
            if (data.code==200) {
                toastr.success('Sub Stage Removed from renewal stages Successfully')
                current.remove();
            }
            else if(data.code==503)
            {
                toastr.error(data.error)
            }
            else
            {
                toastr.error('Error In Removing The Sub Stage Please Try Again After Some Time')
            }
        })
    })
});
