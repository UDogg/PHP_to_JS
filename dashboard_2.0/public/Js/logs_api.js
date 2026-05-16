// $(function(){
//     const apitoken = $("[name='apitoken']").val();
//     console.log(apitoken);
// function url()
//     {
//         console.log('ok');
//         $.ajax({
//             url: "/api/LogsApiList",
//             method: "GET",
//             headers: {
//                 'Authorization': 'Bearer ' + apitoken
//             },
//             success: function (data) {
//                 $('select[name="url"]').empty();
//                 $.each(data.data, function (key, value) {
//                     $('select[name="url"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
//                 });
//             }
//         })
//     }
//     url();
// })
$(document).ready(function () {
// alert('ok');
console.log('Script loaded'); 
// const apitoken = $("[name='apitoken']").val();
    
//         $.ajax({
//             url: "/api/LogsApiList",
//             method: "GET",
//             headers: {
//                 'Authorization': 'Bearer ' + apitoken
//             },
//             success: function(data) {
//                 console.log('AJAX success:', data); 
                
//                 $('select[name="url"]').empty();
//                 $.each(data.data, function(key, value) {
//                     $('select[name="url"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
//                 });
//             },
//             error: function(xhr, status, error) {
//                 console.error('AJAX error:', status, error);
//             }
//         });




//     console.log('API token:', apitoken); 
    
// $(function() {
//     console.log('Script loaded'); 
    
//     const apitoken = $("[name='apitoken']").val();
//     console.log('API token:', apitoken); 
    
//     function url() {
//         console.log('Calling URL function'); 
        
//         $.ajax({
//             url: "/api/LogsApiList",
//             method: "GET",
//             headers: {
//                 'Authorization': 'Bearer ' + apitoken
//             },
//             success: function(data) {
//                 console.log('AJAX success:', data); 
                
//                 $('select[name="url"]').empty();
//                 $.each(data.data, function(key, value) {
//                     $('select[name="url"]').append('<option value="'+ value.id +'">' + value.name + '</option>');
//                 });
//             },
//             error: function(xhr, status, error) {
//                 console.error('AJAX error:', status, error);
//             }
//         });
//     }
    
//     url(); 
// })
});
