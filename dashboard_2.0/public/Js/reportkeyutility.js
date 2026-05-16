$(function(){
    $('.select2').select2({
        closeOnSelect: false
    })
    $(document).ready(function() {
        
        $('.submit_btn').click(function() {
            const keyName = $('[name="key_name"]').val();
            const col = $('[name="columns[]"]').val();

            const isEdit = window.location.pathname.includes('edit');

            if (isEdit) {
                // UPDATE
                $('form[name="key_utility_frm"]').submit();
            } else {
            // CREATE
            var apitokens = $("[name='apitoken']").val();
            $.ajax({
                url: baseUrl +'/api/grouping-key-utility',
                method: 'POST',
                contentType: 'application/json',
                headers: {
                    'Authorization': 'Bearer ' + apitokens
                },
                data: JSON.stringify({ 
                    key_name: keyName,
                    columns: col
                }),
                success: function(response) {
                    toastr.success('Key Created Successfully');
                    setTimeout(() => location.reload(), 1500);
                }
            });
        }
        });
    });

    $(document).ready(function() {
        new Sortable(document.getElementById('sortable-container'), {
            animation: 150,
            ghostClass: 'sortable-ghost',
            handle: '.card-header',
            onEnd: function(evt) {
                var order = [];
                $('#sortable-container .draggable-item').each(function(index) {
                    order.push({
                        id: $(this).data('id'),
                        priority: index + 1
                    });
                });
    
                // Prepare data for application/x-www-form-urlencoded
                var formData = $.param({
                    _token: $('meta[name="csrf-token"]').attr('content'),
                    order: order
                });
    
                $.ajax({
                    url:  baseUrl +'/update-priority', // Replace with your route
                    method: 'POST',
                    data: formData,
                    contentType: 'application/x-www-form-urlencoded',
                    success: function(response) {
                        console.log('Order updated successfully');
                    },
                    error: function(error) {
                        console.error('Error updating order', error);
                    }
                });
            }
        });
    });

    $(document).ready(function() {
        $('.del_icn').on('click', function() {
            var value = $(this).attr('name');
            var apitokens = $("[name='apitoken']").val();
            var payload = {
                key: value
            };
            $.ajax({
                url:  baseUrl + '/api/delete-grouping-key-utility',
                type: 'POST',
                contentType: 'application/json',
                headers: {
                    'Authorization': 'Bearer ' + apitokens
                },
                data: JSON.stringify(payload),
                success: function(response) {
                    toastr.success('All Columns and Key are  Deleted Successfully')
                    setTimeout(function(){
                        location.reload()
                    },1500)
                },
                error: function(xhr, status, error) {
                    console.error('Error:', error);
                }
            });
        });
    });
    $(document).ready(function() {
        $('.del_img').on('click', function() {
            var value = $(this).attr('del_id');
            var payload = {
                key: value
            };
            $.ajax({
                url:  baseUrl + '/api/delete-Single-key',
                type: 'POST',
                contentType: 'application/json',
                data: JSON.stringify(payload),
                success: function(response) {
                    toastr.success('Key Deleted Successfully')
                    setTimeout(function(){
                        location.reload()
                    },1500)
                },
                error: function(xhr, status, error) {
                    console.error('Error:', error);
                }
            });
        });
    });
    
})