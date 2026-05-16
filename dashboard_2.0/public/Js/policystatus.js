function myFunction() {
    document.getElementById("myDropdown").classList.toggle("show");
}

function filterFunction() {
    const input = document.getElementById("myInput");
    const filter = input.value.toUpperCase();
    const div = document.getElementById("myDropdown");
    const a = div.getElementsByTagName("a");
    for (let i = 0; i < a.length; i++) {
        const txtValue = a[i].textContent || a[i].innerText;
        if (txtValue.toUpperCase().indexOf(filter) > -1) {
            a[i].style.display = "";
        } else {
            a[i].style.display = "none";
        }
    }
}

$(document).ready(function() {

    const apitoken = $("[name='apitoken']").val();

    $.ajax({
        url: 'api/policystatus/detailData',
        type: 'POST',
        success: function (data) {
            data.forEach(function (item) {
                const option = $('<option>', {
                    value: item.id,
                    text: item.placeholder_name
                });
                $('#dropdown').append(option);
            });
        }
    });

    var table = $('#data-table').DataTable({
        dom: 'Bfrtip',
        buttons: [{
            extend: 'colvis',
            columns: ':not(:first-child)',
            className: 'buttons-columnVisibility'
        }],
        searching: false, // Disable the search input field
        paging: false,
        searching: false,
        info: false // Disable the "Showing 1 to 10 of 10 entries" message
    });

    // Append buttons to the wrapper
    table.buttons().container().appendTo('.btn_wrapper');

    // Remove dt-button class on button click
    $(document).on('click', '.buttons-columnVisibility', function() {
        $('.buttons-columnVisibility').removeClass('dt-button');
    });

    
    

    $('.filterButton , .sidefilter , .searchButton ').on('click', function(event) {
        event.preventDefault(); // Prevent the default button click behavior
        const token = $('[name="_token"]').val();
        var filterValue = $(this).attr('value');
        var start_date = $(this).attr('startDate');
        var end_date = $(this).attr('endDate');
        var searchValue = $('#searchInput').val(); // Get the value from the input field

    
            var filterKey = $('.filterKey').attr('name');
            var filterValue = $('.filterKey').val();
        

        $.ajax({
            url: 'api/policystatus/policystatus', 
            method: 'POST',
            headers:{
                'Content-Type': 'application/json',
                'Authorization': 'Bearer ' + apitoken
            },
            data: {
                _token: token, // Include the CSRF token for Laravel
                filter_value: filterValue,
                start_date: start_date,
                end_date: end_date,
                search: searchValue
            },
            success: function(response) {
                var data = response.data.data;
                var table = $("#data-table");
                var tablebody = $("#data-table tbody");
                var tablehead = $("#data-table thead");
                
                // Clear the table headers and body before inserting new data
                tablehead.empty();
                tablebody.empty();
            
                if (data.length > 0) {
                    var headerRow = $("<tr></tr>");
                    
                    // Create headers from the keys of the first object
                    Object.keys(data[0]).forEach(function(key) {
                        if (key !== 'proposal_url' && key !== 'quote_url') {
                            headerRow.append($("<th></th>").text(key));
                        }
                    });
            
                    tablehead.append(headerRow);
            
                    // Populate the table body with data
                    data.forEach(function(item) {
                        var row = $("<tr></tr>");
                        
                        Object.keys(item).forEach(function(key) {
                            if (key !== 'proposal_url' && key !== 'quote_url') {
                                row.append($("<td></td>").text(item[key] || ''));
                            }
                        });
            
                        tablebody.append(row);
                    });
                } else {
                    // Handle case where there's no data
                    tablebody.append($("<tr><td colspan='100%'>No data available</td></tr>"));
                }
            },
            
            
            error: function(xhr, status, error) {
                // Handle any errors here
                console.log(error);
            }
        });
    });

     $('.excel').on('click', function () {
        const token = $('[name="_token"]').val();
        var excel = $(this).attr('value');
    
        $.ajax({
            url: 'api/policystatus/policystatus',
            method: 'POST',
            headers:{
                'Content-Type': 'application/json',
                'Authorization': 'Bearer ' + apitoken
            },
            data: {
                excelExport: excel
            },
            xhrFields: {
                responseType: 'blob' // Important for handling binary data
            },
            success: function (data, status, xhr) {
                // Get the filename from the response headers if available
                var filename = xhr.getResponseHeader('Content-Disposition')
                    .split(';')[1].split('=')[1].replace(/"/g, '') || 'download.xlsx';
    
                // Create a new Blob object using the data from the response
                var blob = new Blob([data], { type: 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet' });
    
                // Create a link element, set the download attribute with the filename, and trigger a click
                var link = document.createElement('a');
                link.href = window.URL.createObjectURL(blob);
                link.download = filename;
                document.body.appendChild(link);
                link.click();
                document.body.removeChild(link);
            },
            error: function (xhr, status, error) {
                console.log('Error:', error);
            }
        });
    });

    
});



