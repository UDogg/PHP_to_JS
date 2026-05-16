
$(function () {
    $('.verticaleditbtn').on('click', function () {
        const token = $('[name="_token"]').val();
        var id = $(this).attr('data-ic');
        var type = $(this).attr('data-type');
        // var record = $(this).attr('data-total_record');
        var type = $(this).attr('data-type');
        var start_date = $(this).attr('start_date');
        var end_date = $(this).attr('end_date');
        var section = $(this).attr('section');
        var total_record = $(this).attr('total_record');


        $.ajax({
            url: 'edit',
            method: 'POST',
            data: {
                _token: token,
                data: {
                    ic: id,
                    type: type,
                    // total_record: record,
                    start_date: start_date,
                    end_date: end_date,
                    section: section,
                    record: total_record

                }


            },
            success: function (response) {
                data = response.data
                var tablebody = $("#example1 tbody");
                tablebody.empty()

                data.forEach(function (item, index) {

                    var row = $("<tr></tr>");
                    row.append($("<td></td>").text(index + 1));
                    row.append($("<td></td>").text(item["Logs link"]));
                    row.append($("<td></td>").text(item.enquiry_id));
                    row.append($("<td></td>").text(item.ic_name));
                    row.append($("<td></td>").text(item.vehicle_type));
                    row.append($("<td></td>").text(item.make));
                    row.append($("<td></td>").text(item.model));
                    row.append($("<td></td>").text(item.variant));
                    row.append($("<td></td>").text(item.version_id));
                    row.append($("<td></td>").text(item.fuel_type));
                    row.append($("<td></td>").text(item.vehicle_register_date));
                    row.append($("<td></td>").text(item.manufacture_year));
                    row.append($("<td></td>").text(item.insurer_modelid));
                    row.append($("<td></td>").text(item.lead_id));
                    row.append($("<td></td>").text(item.quote_reference_no));
                    row.append($("<td></td>").text(item.insurer_quote_id));
                    row.append($("<td></td>").text(item.response_time));
                    row.append($("<td></td>").text(item.previous_policy_type));
                    row.append($("<td></td>").text(item.previous_policy_expiry_date));
                    row.append($("<td></td>").text(item.case_type));
                    row.append($("<td></td>").text(item.plan_name));
                    row.append($("<td></td>").text(item.policy_type));
                    row.append($("<td></td>").text(item.rto));
                    row.append($("<td></td>").text(item.idv));
                    row.append($("<td></td>").text(item.quote_response));
                    row.append($("<td></td>").text(item.actionable_at));
                    row.append($("<td></td>").text(item.error_type));
                    row.append($("<td></td>").text(item.error_category));
                    row.append($("<td></td>").text(item.premium));
                    row.append($("<td></td>").text(item.Date));
                    row.append($("<td></td>").text(item.Time));
                    row.append($("<td></td>").text(item.registration_number));
                    // row.append($("<td></td>").text(item.dashboard_count));
                    tablebody.append(row);

                });
            }
        });
        $('#exampleModal').modal('show');
    });
    $('.failurebtn').on('click', function () {
        const token = $('[name="_token"]').val();
        var id = $(this).attr('data-ic');
        var type = $(this).attr('data-type');
        // var record = $(this).attr('data-total_record');
        var type = $(this).attr('data-type');
        var start_date = $(this).attr('start_date');
        var end_date = $(this).attr('end_date');
        var section = $(this).attr('section');
        var total_record = $(this).attr('total_record');


        $.ajax({
            url: 'edit',
            method: 'POST',
            data: {
                _token: token,
                data: {
                    ic: id,
                    type: type,
                    // total_record: record,
                    start_date: start_date,
                    end_date: end_date,
                    section: section,
                    record: total_record

                }


            },
            success: function (response) {
                data = response.data
                var tablebody = $("#example1 tbody");
                tablebody.empty()

                data.forEach(function (item, index) {

                    var row = $("<tr></tr>");
                    row.append($("<td></td>").text(index + 1));
                    row.append($("<td></td>").text(item["Logs link"]));
                    row.append($("<td></td>").text(item.enquiry_id));
                    row.append($("<td></td>").text(item.ic_name));
                    row.append($("<td></td>").text(item.vehicle_type));
                    row.append($("<td></td>").text(item.make));
                    row.append($("<td></td>").text(item.model));
                    row.append($("<td></td>").text(item.variant));
                    row.append($("<td></td>").text(item.version_id));
                    row.append($("<td></td>").text(item.fuel_type));
                    row.append($("<td></td>").text(item.vehicle_register_date));
                    row.append($("<td></td>").text(item.manufacture_year));
                    row.append($("<td></td>").text(item.insurer_modelid));
                    row.append($("<td></td>").text(item.lead_id));
                    row.append($("<td></td>").text(item.quote_reference_no));
                    row.append($("<td></td>").text(item.insurer_quote_id));
                    row.append($("<td></td>").text(item.response_time));
                    row.append($("<td></td>").text(item.previous_policy_type));
                    row.append($("<td></td>").text(item.previous_policy_expiry_date));
                    row.append($("<td></td>").text(item.case_type));
                    row.append($("<td></td>").text(item.plan_name));
                    row.append($("<td></td>").text(item.policy_type));
                    row.append($("<td></td>").text(item.rto));
                    row.append($("<td></td>").text(item.idv));
                    row.append($("<td></td>").text(item.quote_response));
                    row.append($("<td></td>").text(item.actionable_at));
                    row.append($("<td></td>").text(item.error_type));
                    row.append($("<td></td>").text(item.error_category));
                    row.append($("<td></td>").text(item.premium));
                    row.append($("<td></td>").text(item.Date));
                    row.append($("<td></td>").text(item.Time));
                    row.append($("<td></td>").text(item.registration_number));
                    // row.append($("<td></td>").text(item.dashboard_count));
                    tablebody.append(row);

                });
            }
        });
        $('#failureModal').modal('show');
    });

    // download excel
    $('.downloadbtn').on('click', function () {
        const token = $('[name="_token"]').val();
        var id = $(this).attr('data-ic');
        var type = $(this).attr('data-type');
        var start_date = $(this).attr('start_date');
        var end_date = $(this).attr('end_date');
        var section = $(this).attr('section');
        var total_record = $(this).attr('total_record');
    
        $.ajax({
            url: 'download',
            method: 'POST',
            data: {
                _token: token,
                ic: id,
                type: type,
                start_date: start_date,
                end_date: end_date,
                section: section,
                record: total_record
            },
            xhrFields: {
                responseType: 'blob' // Important to handle file download
            },
            success: function (response, status, xhr) {
                if (xhr.getResponseHeader('content-type') === 'application/json') {
                    // Handle error message
                    var reader = new FileReader();
                    reader.onload = function () {
                        var data = JSON.parse(reader.result);
                        if (data.status === 'error') {
                            alert(data.message); // Show alert if data is not found
                        }
                    };
                    reader.readAsText(response);
                } else {
                    // Create a link to download the file
                    var a = document.createElement('a');
                    var url = window.URL.createObjectURL(response);
                    a.href = url;
                    a.download = 'motor_data.xlsx';
                    document.body.append(a);
                    a.click();
                    a.remove();
                    window.URL.revokeObjectURL(url);
                }
            },
            error: function (xhr) {
                alert('An error occurred while downloading the file.');
            }
        });
    });
    
    

});