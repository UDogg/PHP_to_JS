$(document).ready(function () {

    const token = $('meta[name="csrf-token"]').attr('content');

    // ================= ADD =================
    $('#addForm').submit(function (e) {
        e.preventDefault();

        $.ajax({
            url: '/da/mongo-key-utility',
            type: 'POST',
            data: $(this).serialize(),
            success: function () {
                $('#addModal').modal('hide');
                location.reload();
            },
            error: function (err) {
                console.log(err);
            }
        });
    });

    // ================= EDIT CLICK =================
    $('.editBtn').click(function () {
        let id = $(this).data('id');

        $.get('/da/mongo-key-utility/' + id, function (res) {

            let data = res.data;

            $('#edit_id').val(data.id);
            $('#edit_column_name').val(data.column_name);
            $('#edit_is_default').val(data.is_default);
            $('#edit_is_visible').val(data.is_visible);
            $('#edit_alias').val(data.alias);
            $('#edit_lob').val(data.lob);
            $('#edit_stage').val(data.stage);

            $('#editModal').modal('show');
        });
    });

    // ================= UPDATE =================
    $('#editForm').submit(function (e) {
        e.preventDefault();

        let id = $('#edit_id').val();

        $.ajax({
            url: '/da/mongo-key-utility/' + id,
            type: 'POST',
            data: {
                _token: token,
                _method: 'PUT',
                column_name: $('#edit_column_name').val(),
                is_default: $('#edit_is_default').val(),
                is_visible: $('#edit_is_visible').val(),
                alias: $('#edit_alias').val(),
                lob: $('#edit_lob').val(),
                stage: $('#edit_stage').val()
            },
            success: function () {
                $('#editModal').modal('hide');
                location.reload();
            }
        });
    });

    // ================= DELETE =================
    $('.deleteBtn').click(function () {

        if (!confirm('Delete this record?')) return;

        let id = $(this).data('id');

        $.ajax({
            url: '/da/mongo-key-utility/' + id,
            type: 'POST',
            data: {
                _token: token,
                _method: 'DELETE'
            },
            success: function () {
                location.reload();
            }
        });
    });

});