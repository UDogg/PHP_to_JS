$(document).ready(function() {
    $('#lobSelect').on('change', function() {
        var lobId = $(this).val();
        var token = $('meta[name="csrf-token"]').attr('content');
        if (lobId) {
            $.ajax({
                url: baseUrl + '/excel-upload/excel_column_master',
                type: 'POST',
                contentType: 'application/json',
                headers: {
                    'X-CSRF-TOKEN': token
                },
                data: JSON.stringify({ lob_id: lobId }),
                success: function(response) {
                    var tableBody = $('#tableBody');
                    tableBody.empty();

                    // Loop through allColumns to generate the rows
                    $.each(response.allColumns, function(index, item) {
                        var row = '<tr>';

                        // Get matched data using column_name
                        var matchedValue = response.matchedData[item.column_name] || '';

                        row += '<td>' + item.column_name + '</td>';
                        row += '<td>' + matchedValue + '</td>';
                        row += '<td><input type="text" name="excel_column_name[]" value="' + (item.excel_column_name ? item.excel_column_name : '') + '"></td>';
                        row += '<td><input type="number" name="sequence[]" value="' + (item.sequence ? item.sequence : '') + '"></td>';
                        row += '<td><input type="hidden" name="excel_key_master_id[]" value="' + item.excel_key_master_id + '"></td>';
                        row += '</tr>';

                        tableBody.append(row);
                    });
                },
                error: function(error) {
                    console.error('Error fetching data:', error);
                }
            });
        }
    });
});
$(document).ready(function() {
    $("#submit").click(function(e) {
        e.preventDefault();
       
        var excel_column_nam = $("[name='excel_column_name[]']").map(function() {
            return $(this).val();
        }).get();

        var sequence = $("[name='sequence[]']").map(function() {
            return $(this).val();
        }).get();
        var excel_key_master_id = $("[name='excel_key_master_id[]']").map(function() {
            return $(this).val();
        }).get();
        var token = $('meta[name="csrf-token"]').attr('content');
        console.log(token)
        // Prepare the data object
        var data = {
            excel_column_name: excel_column_nam,
            sequence: sequence,
            excel_key_master_id: excel_key_master_id
            // Include other necessary data here
        };

        $.ajax({
            url: baseUrl + '/excel-upload/UpdateColumnNameToExcel',
            type: 'POST',
            contentType: 'application/json; charset=UTF-8',
            dataType: 'json',
            headers: {
                'X-CSRF-TOKEN': token ,
                'X-Requested-With': 'XMLHttpRequest'
            },
            data: JSON.stringify(data),
            success: function(response) {
                try {
                    var data = response;
                    console.log(data);
                } catch (e) {
                    toastr.error('Some Error Occurred. Please Try Again Later.');
                    return false;
                }

                if (data.status === 'true') {
                    toastr.success('Column Updated Successfully');
                    location.reload();
                } else if (data.message !== '') {
                    toastr.error(data.message);
                    return false;
                } else {
                    toastr.error('Some Error Occurred. Please Try Again Later.');
                    location.reload();
                    return false;
                }
            },
            error: function(xhr, status, error) {
                toastr.error('Request failed: ' + error);
            }
        });
    });
});



