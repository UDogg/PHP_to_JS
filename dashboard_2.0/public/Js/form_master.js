
    $(document).ready(function () {
        $.ajaxSetup({
            headers: {
                'X-CSRF-TOKEN': $('meta[name="csrf-token"]').attr('content')
            }
        });

        // Fetch items for the dropdown
        $.ajax({
            url: 'get_items',
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

        // Fetch all submissions and display them
        function loadSubmissions() {
            $.ajax({
                url: 'show_form',
                type: 'post',
                success: function (data) {
                    let tableBody = $('#submissions-table-body');
                    tableBody.empty();
                    data.forEach(function (submission) {
                        tableBody.append(`
                            <tr>
                                <td>${submission.label_name}</td>
                                <td>${submission.item_value}</td>
                                <td>
                                    <button class="btn btn-primary btn-sm edit-button" data-id="${submission.id}">Edit</button>
                                    <button class="btn btn-danger btn-sm delete-button" data-id="${submission.id}">Delete</button>
                                </td>
                            </tr>
                        `);
                    });
                }
            });
        }

        loadSubmissions();

        // Handle form submission (Create and Update)
        $('#form').on('submit', function (e) {
            e.preventDefault();
            const action = $(this).attr('action') || 'submit_form';
            const method =  'POST';
            $.ajax({
                url: action,
                type: method,
                data: $('#form').serialize(),
                success: function (response) {
                    toastr.success(method === 'POST' ? 'Data saved successfully!' : 'Data updated successfully!');
                    $('#label_name').val('');
                    $('#dropdown').val('');
                    $('#form').removeAttr('action');
                    loadSubmissions();
                },
                error: function (response) {
                    toastr.error('Error in saving/updating data. Please try again later.');
                }
            });
        });

        // Handle delete button click
        $(document).on('click', '.delete-button', function () {
            const id = $(this).data('id');
            $.ajax({
                url: 'destroy_form' + id,
                type: 'DELETE',
                success: function () {
                    toastr.success('Data deleted successfully!');
                    loadSubmissions();
                },
                error: function () {
                    toastr.error('Error in deleting data. Please try again later.');
                }
            });
        });

        // Handle edit button click
        $(document).on('click', '.edit-button', function () {
            const id = $(this).data('id');
            $.ajax({
                url: 'edit/' + id,
                type: 'GET',
                success: function (submission) {
                    $('#editModal').modal('show');
                    $('#label_name').val(submission.label_name);
                    $('#dropdown').val(submission.item_id);
                    $('#form').attr('action', '{{ url("update") }}/' + submission.id);
                }
            });
        });
    });
