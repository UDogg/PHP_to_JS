@extends('layout.app', ['title' => 'Logs Api'])
<!-- Main content -->
@section('content')
<style>
    .pagination-container {
        display: flex;
        flex-direction: column;
        align-items: center;
    }

    .btn-group .btn {
        margin: 0 5px;
        color: #000;
        background-color: gray;
    }
</style>

    <section class="content">
        <div class="card card-secondary">
            <div class="card-header bg-secondary text-white">
                <h3 class="card-title">Logs Api</h3>
            </div>
            <div class="card-body">
                <div class="row mb-3">
                    <div class="col-md-4">
                        <input 
                            type="text" 
                            name="search" 
                            class="form-control" 
                            placeholder="Search URL, Method, Header, Request, Response, Api Type"
                        >
                    </div>
                </div>
                

            <!-- Logs Table -->
            <table class="table table-bordered">
                <thead class="table-dark">
                    <tr>
                        <th>URL</th>
                        <th>Method</th>
                        <th>Header</th>
                        <th>Request</th>
                        <th>Response</th>
                        <th>Status Code</th>
                        <th>Api Type</th>
                    </tr>
                </thead>
                <tbody>
                    @if(isset($logs) && count($logs) > 0)
                        @foreach ($logs as $log)
                            <tr>
                                <td>{{ $log->url }}</td>
                                <td>{{ $log->method }}</td>
                                <td>{{ $log->headers }}</td>
                                <td>{{ $log->request }}</td>
                                <td>{{ $log->response }}</td>
                                <td>{{ $log->status_code }}</td>
                                <td>{{ $log->api_type }}</td>
                            </tr>
                        @endforeach
                    @else
                        <tr>
                            <td colspan="6" class="text-center">No data available.</td>
                        </tr>
                    @endif
                </tbody>
            </table>

            <div class="pagination-container text-center mb-4">
                <div class="pagination-summary mb-3"></div>
                <div class="btn-group">
                    <button id="prev-page" class="btn btn-outline-secondary" disabled>Previous</button>
                    <button id="next-page" class="btn btn-outline-secondary" disabled>Next</button>
                    <button id="last-page" class="btn btn-outline-secondary">Last</button>
                </div>
            </div>
            
        </div>
    </div>
</section>

<script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
<script>
    $(document).ready(function () {
    const searchInput = $('input[name="search"]');
    const prevButton = $('#prev-page');
    const nextButton = $('#next-page');
    const lastButton = $('#last-page');
    const paginationSummary = $('.pagination-summary');

    // Function to fetch and update logs
    function fetchLogs(url) {
        const searchQuery = searchInput.val();

        $.ajax({
            url: url, 
            type: "GET",
            data: { search: searchQuery },
            success: function (response) {
                const tableBody = $('table tbody');
                const paginationWrapper = $('.pagination-wrapper');

                // Clear the table body and pagination
                tableBody.empty();

                if (response.data && response.data.length > 0) {
                    // Populate the table with logs
                    response.data.forEach(log => {
                        tableBody.append(`
                            <tr>
                                <td>${log.url}</td>
                                <td>${log.method}</td>
                                <td>${log.headers}</td>
                                <td>${log.request}</td>
                                <td>${log.response}</td>
                                <td>${log.status_code}</td>
                                <td>${log.api_type}</td>
                            </tr>
                        `);
                    });

                    // Update pagination buttons
                    prevButton.prop('disabled', !response.pagination.prev_page_url);
                    nextButton.prop('disabled', !response.pagination.next_page_url);
                    lastButton.prop('disabled', !response.pagination.last_page_url);

                    // Update button URLs
                    prevButton.data('url', response.pagination.prev_page_url);
                    nextButton.data('url', response.pagination.next_page_url);
                    lastButton.data('url', response.pagination.last_page_url);

                    // Update pagination summary
                    updatePaginationSummary(response.pagination);
                } else {
                    tableBody.append('<tr><td colspan="7" class="text-center">No data available.</td></tr>');
                    resetPaginationSummary();
                }
            },
            error: function () {
                alert('Failed to fetch logs. Please try again.');
            }
        });
    }

    // Function to update pagination summary
    function updatePaginationSummary(pagination) {
        paginationSummary.html(`
            Page ${pagination.current_page} of ${pagination.total_pages}, 
            showing ${pagination.per_page} records per page out of ${pagination.total_records} total.
        `);
    }

    // Function to reset pagination summary
    function resetPaginationSummary() {
        paginationSummary.text('No data available.');
    }

    // Event listener for buttons
    prevButton.on('click', function () {
        const url = $(this).data('url');
        if (url) fetchLogs(url);
    });

    nextButton.on('click', function () {
        const url = $(this).data('url');
        if (url) fetchLogs(url);
    });

    lastButton.on('click', function () {
        const url = $(this).data('url');
        if (url) fetchLogs(url);
    });

    // Handle input change for search
    searchInput.on('input', function () {
        fetchLogs("{{ route('LogsApiList') }}");
    });

    // Initial fetch
    fetchLogs("{{ route('LogsApiList') }}");
});

</script>

    {{-- <script src="{{ asset('Js/logs_api.js') }}"></script> --}}
    
    {{-- <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script> --}}
<script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
