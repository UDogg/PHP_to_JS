{{-- partials/cta_table_rows.blade.php --}}
@if(isset($cta) && count($cta) > 0)
    @foreach ($cta as $ctas)
        <tr>
            <td>{{ $ctas->lob }}</td>
            <td>{{ $ctas->stage }}</td>
            <td>{{ $ctas->cta_name }}</td>
            <td>{{ $ctas->redirection_url }}</td>

            <td>
                <button class="btn btn-sm btn-primary edit-section-field"
                    data-id="{{ $ctas->id }}"
                    data-name="{{ $ctas->lob_id }}"
                    data-key="{{ $ctas->stage_id }}"
                    data-value="{{ $ctas->cta_id }}"
                    data-url="{{ $ctas->redirection_url }}"
                    data-toggle="modal"
                    data-target="#editFieldModal">
                    Edit
                </button>
                <button class="btn btn-sm btn-danger" data-id="{{ $ctas->id }}" id="delete-sst">
                    Delete
                </button>
            </td>
        </tr>
    @endforeach
@else
    <tr>
        <td colspan="9" class="text-center">No data available for the selected LOB.</td>
    </tr>
@endif
