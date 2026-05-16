$(function(){
    $(".subbtn").click(function(){
        if($('[name="query"]').val() == ""){
            toastr.error("Please Enter Sql");
            $('[name="query"]').focus();
            return false
        }
        else
        {
            $.post('SqlRunner',$("[name='sql_runner']").serialize(),function(res){
                console.log(res);
            })
        }
    })
})
