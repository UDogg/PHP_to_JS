$(document).ready(function() {
    // Set CSRF token in the AJAX request headers
    $.ajaxSetup({
        headers: {
            'X-CSRF-TOKEN': $('meta[name="csrf-token"]').attr('content')
        }
    });

    $('#field-type').on('change', function() {
        const selectOptions = $('#select-options');
        if (this.value === 'select') {
            selectOptions.show();
        } else {
            selectOptions.hide();
        }
    });

    $('#add-field').on('click', function() {
        const fieldType = $('#field-type').val();
        const placeholder = $('#placeholder').val();
        const mandatory = $('#mandatory').is(':checked');
        const size = $('#size').val();
        let selectValues = [];
        let multiselect = false;
        if (fieldType === 'select') {
            selectValues = $('#select-values').val().split(',').map(val => val.trim());
            multiselect = $('#multiselect').is(':checked');
        }

        // AJAX call to send data to the server
        $.ajax({
            url: 'update_form',
            type: 'POST',
            data: {
                field_type: fieldType,
                placeholder: placeholder,
                mandatory: mandatory,
                size: size,
                select_values: selectValues,
                multiselect: multiselect
            },
            success: function (data) {
                if (data.status == 200) {
                    toastr.success('Key and columns are  Updated Successfully')

                } else {
                    toastr.error('Error In Updating The Key Please Try Again After Some Time')
                }
            }
        });
    });
});
