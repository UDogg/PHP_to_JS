$(document).ready(function () {

        $.ajax({
        url: 'miscolumnview/mongo-keys',
        type: "GET",
        success: function (response) {
    
            if (response.status !== 200) {
                alert("Failed to load Mongo keys");
                return;
            }

            let allKeys = [];
    
            response.return_data.forEach(item => {
                allKeys.push(...item.column_names);
            });
    
            allKeys = [...new Set(allKeys)].sort();
    
            let options = `<option value="">Select Mongo Key</option>`;
    
            allKeys.forEach(col => {
                options += `<option value="${col}">${col}</option>`;
            });
    
            $("#mongo_key").html(options);
        }
   });


    $(document).on("click", ".editBtn", function () {

        let item = $(this).data("item");
    
        setTimeout(function () {
            $("#mongo_key").val(item.mongo_key);
        }, 400);
    
        $("#existing_value").val(item.existing_value);
        $("#new_value").val(item.new_value);
    
        $("#edit_id").val(item.id);
        $("#misForm").attr("action", 'miscolumnview/update/' + item.id);
        $("#submitBtn").text("Update");
    
        $('html, body').animate({ scrollTop: 0 }, 'slow');
    });

    $(".deleteBtn").on("click", function (e) {
        if (!confirm("Are you sure you want to delete this record?")) {
            e.preventDefault();
        }
    });

});
