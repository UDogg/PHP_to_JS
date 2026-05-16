$(document).ready(function () {
    $.ajaxSetup({
        headers: {
            'X-CSRF-TOKEN': $('meta[name="csrf-token"]').attr('content')
        }
    });

    $('#search-btn').on('click', function () {
        const selectedConfigId = $('#lob-filter').val();
        const searchQuery = $('#search-input').val();
        const APP_URL = $('meta[name="app-url"]').attr('content');
    
        $.ajax({
            url: APP_URL + '/credential/filter',
            type: 'POST',
            data: {
                config_id: selectedConfigId,
                search: searchQuery
            },
            success: function (response) {
                const tableBody = $('#example1');
                tableBody.empty();
    
                if (response.filteredCredentials.length > 0) {
                    $.each(response.filteredCredentials, function (index, credential) {
                        const row = `
                            <tr data-id="${credential.credential_id}">
                                <td>
                                    <a href="${APP_URL}/credential/${credential.credential_id}/edit" class="btn btn-sm btn-outline-info editbtn">
                                        <i class="fa-solid fa-pen-to-square"></i>
                                    </a>
                                    <button class="btn btn-sm btn-outline-danger delete-btn mt-2" data-id="${credential.credential_id}">
                                        <i class="fa-solid fa-trash"></i>
                                    </button>
                                </td>
                                <td>${credential.credential_label}</td>
                                <td>${credential.credential_key}</td>
                                <td>${credential.credential_value}</td>
                                <td>${credential.enviroment}</td>
                                <td>${credential.created_at}</td>
                                <td>${credential.updated_at}</td>
                            </tr>`;
                        tableBody.append(row);
    
                        $(`.delete-btn[data-id="${credential.credential_id}"]`).on('click', function () {
                            const id = $(this).data('id');
                            if (confirm('Are you sure you want to delete this credential?')) {
                                $.ajax({
                                    url: APP_URL+ `/credential/${id}`,
                                    type: 'POST',
                                    data: {
                                        _method: 'DELETE',
                                        _token: $('meta[name="csrf-token"]').attr('content')
                                    },
                                    success: function () {
                                        $(`tr[data-id="${id}"]`).remove();
                                        window.location.reload();
                                    },
                                    error: function (xhr) {
                                        console.error('Delete error:', xhr.responseText);
                                        alert('Failed to delete credential.');
                                    }
                                });
                            }
                        });
                    });
                } else {
                    tableBody.append('<tr><td colspan="7" class="text-center">No credentials found</td></tr>');
                }
            },
            error: function (xhr) {
                console.error('AJAX error:', xhr.responseText);
            }
        });
    });
    
    
    
});
