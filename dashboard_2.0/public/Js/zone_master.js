$(function () {


    $('.verticaleditbtn').on('click', function() {
        $('#vid').val($(this).data('id'));
        $('#vname').val($(this).data('name'));
        $('#editverticalModel').modal('show');
    });

    $('#editVerticalForm').on('submit', function(e) {
        e.preventDefault();
        const token = $('[name="_token"]').val();
        let id = $('#vid').val();
        let name = $('#vname').val();

        $.ajax({
            url: 'api/zone_master/vertical_master/update', // Backend route to handle update
            method: 'POST',
            data: {
                _token: token,
                id: id,
                name: name,
            },
            success: function(response) {
                // Handle success response
                location.reload();
            }
        });
    });


    $('.verticalbtn').on('click', function () {
        $('#exampleModal').modal('show');
    });

    $('#vform').on('submit', function(e) {
        e.preventDefault();
        var token = $('[name="_token"]').val();
        let verticalName = $('#verticalName').val();

        $.ajax({
            url: 'api/zone_master/vertical', 
            method: 'POST',
            data: {
                _token: token,
                verticalName: verticalName,
            },
            success: function(data) {
                if (data.status == 200) {
                    toastr.success('Vertical Name Added Successfully')

                } else {
                    toastr.error('Error In Updating The Key Please Try Again After Some Time')
                }
            }
        });
    });

    $('.verticaldeletebtn').on('click', function () {
        const token = $('[name="_token"]').val();
        let id = $(this).data('id');

        if (confirm('Are you sure you want to delete this data?')) {
            $.ajax({
                url: 'api/zone_master/vertical_master/delete', // Backend route to handle delete
                method: 'POST',
                data: {
                    _token: token,
                    id: id
                },
                success: function (response) {
                    // Handle success response
                    location.reload();
                }
            });
        }
    });





    $('.editbtn').on('click', function () {
        var id = $(this).data('id');
    
        $.ajax({
            url: APP_URL + '/zone_master/edit/' + id, 
            method: 'GET', 
            success: function (response) {
                if (response.status == 200) {
                    let data = response.data;
                    $("[name='id']").val(data.id);
                    $("[name='off_zone']").val(data.office_zone);
                    $("[name='off_name']").val(data.office_name);
                    $("[name='parent_office']").val(data.parent_office);
                    $("[name='office_pincode']").val(data.office_pincode);
                    $("[name='contact_phone']").val(data.contact_phone);
                    $("[name='contact_email']").val(data.contact_email);
                    $("[name='address']").val(data.address);
    
                    $('#editModal').modal('show');
                } else {
                    toastr.error('Failed to load data.');
                }
            },
            error: function (xhr) {
                toastr.error('Error fetching data.');
            }
        });
    });
    

    // Update data
    $('#editForm').on('submit', function (e) {
        e.preventDefault(); 
    
        let id = $("[name='id']").val(); 
        const token = $('meta[name="csrf-token"]').attr('content');  
        let formData = $(this).serialize() + "&_token=" + token; 
    
        $.ajax({
            url: APP_URL + '/zone_master/update', 
            method: 'PUT', 
            data: formData,
            success: function (response) {
                toastr.success('Zone Master Updated Successfully');
                $('#editModal').modal('hide'); 
                location.reload();
            },
            error: function (xhr) {
                toastr.error(xhr.responseJSON.error || 'Something went wrong');
            }
        });
    });


    $('.deletebtn').on('click', function () {
        const token = $('meta[name="csrf-token"]').attr('content');  
        let id = $(this).data('id');

        if (confirm('Are you sure you want to delete this data?')) {
            $.ajax({
                url: APP_URL + '/zone_master/delete',
                method: 'POST',
                data: {
                    _token: token,
                    id: id
                },
                success: function(response) {
                    alert(response.success);
                    location.reload();
                },
                error: function(xhr) {
                    alert(xhr.responseJSON.error || "Something went wrong");
                }
            });
            
        }
    });

    $(".submit_btn").click(function () {
        const token = $('meta[name="csrf-token"]').attr('content');  

        var data = $("[name='zoneMaster']").serialize();
        $.ajax({
            url: APP_URL +  '/zone_master',
            method: 'post',
            data: data,
            headers:{
                'Authorization': 'Bearer ' + token
            },
            success: function (data) {
                if (data.status == 200) {
                    toastr.success('Zone Master Added Successfully')
                    location.reload();

                } else {
                    toastr.error('Error In Updating Try Again After Some Time')
                }
            }
        })
    })
})