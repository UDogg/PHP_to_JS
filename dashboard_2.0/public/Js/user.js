// $(function(){
//     const apitoken = $("[name='apitoken']").val();
//     function getRoles(usertype) {
//         $.ajax({
//             url: "{{app_url}}/api/roles/list",
//             method: "GET",
//             data:{
//                 usertype : usertype ?? ''
//             },
//             headers: {
//                 'Authorization': 'Bearer ' + apitoken
//             },
//             success: function (data) {
//                 $('select[name="role_id"]').empty();
//                 $.each(data.data, function (key, value) {
//                     $('select[name="role_id"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
//                 });
//             }
//         })
//     }
//     getRoles('');
//     $("[name='user_type']").change(function (){
//         getRoles($("[name='user_type']").val());
//     })
//     function getLOB()
//     {
//         $.ajax({
//             url: "{{app_url}}/api/lob/list",
//             method: "GET",
//             headers: {
//                 'Authorization': 'Bearer ' + apitoken
//             },
//             success: function (data) {
//                 $('select[name="lob_id"]').empty();
//                 $.each(data.data, function (key, value) {
//                     $('select[name="lob_id"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
//                 });
//             }
//         })
//     }
//     getLOB();
//     $('#mobile').on('input', function() {
//         let value = $(this).val();
//         value = value.replace(/\D/g, '');
//         if (value.length > 10) {
//             value = value.slice(0, 10);
//         }
//         $(this).val(value);
//     });
//     $('#pincode').on('input', function() {
//         let value = $(this).val();
//         value = value.replace(/\D/g, '');
//         if (value.length > 6) {
//             value = value.slice(0, 6);
//         }
//         $(this).val(value);
//     });
//     $.ajax({
//         url: "{{app_url}}/api/UserType/list",
//         method: 'GET',

//         headers:{
//             'Authorization': 'Bearer ' + apitoken
//         },
//         success: function(data) {
//             $.each(data.data, function (key, value) {
//                 $('select[name="user_type"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
//             });
//         }
//     })
//     $("[name='sb_btn']").click(function (){
//         const formdata = $("[name='usercreation']").serialize();
//         const token = $("[name='apitoken']").val()
//         $.ajax({
//             url: "{{app_url}}/api/users/create",
//             type: "POST",
//             data: formdata,
//             headers:{
//                 'Authorization': 'Bearer ' + token
//             },
//             success: function (data) {
//                 if (data.status == 200) {
//                     // location.reload();
//                     toastr.success("User Created SuccessFully")
//                 }
//                 else
//                 {
//                     toastr.error(data.message)
//                     return false;
//                 }

//             }
//         })
//     })

//         $.ajax({
//             url: "{{app_url}}/api/users/list",
//             method: "GET",
//             headers: {
//                 'Authorization': 'Bearer ' + apitoken
//             },

//             success: function(data) {

//                 console.log('data checking');
//                 $('select[name="reportingto"]').empty();
//                 $('select[name="reportingto"]').append('<option value="">select Reporting To</option>');
//                 $.each(data.data, function(key, user) {
//                     $('select[name="reportingto"]').append('<option value="'+ user.id +'">' + user.name + '</option>');
//                 });

//                 var selectedReportingTo = "{{ old('reportingto', $user->reportingto ?? '') }}";
//                 if (selectedReportingTo) {

//                     $('select[name="reportingto"]').val(selectedReportingTo);
//                 }
//             }
//         });
// })

