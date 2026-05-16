@extends('layout.app', ['pageTitle' => 'Email Logs', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
<!-- Main content -->
@section('content')
<style>
    .pagination-wrapper {
  display: flex;
  justify-content: center;
}

.pagination {
  list-style: none;
  display: flex;
  justify-content: center;
}

.pagination li {
  margin: 0 5px;
}

.pagination li.active a {
  font-weight: bold;
}

.pagination li.disabled a {
  color: gray;
  pointer-events: none;
}
</style>
    <section class="content">
        <div class="container-fluid">
            <div class="row">
                <div class="col-12">
                    <div class="card">

                        <!-- /.card-header -->
                        <div class="card-body">
                            <table id="example" class="table table-bordered table-striped">
                                <thead>
                                    <tr>

                                        @foreach ($columns as $column)
                                            <th>{{ $column }}</th>
                                        @endforeach
                                        <th>Action</th>
                                    </tr>
                                </thead>
                                <tbody>
                                    @foreach ($logs as $log)
                                        <tr>
                                            {{-- <td>{{ $log->email_id}}</td> --}}
                                            <td>{{ $log->email }}</td>
                                            <td>{{ $log->subject }}</td>
                                            <td>{{ $log->type }}</td>
                                            <td>{{ $log->status }}</td>
                                            <td>{{ \Carbon\Carbon::parse($log->sent_at)->format('d/m/Y') }}</td>
                                            <td>{{ \Carbon\Carbon::parse($log->created_at)->format('d/m/Y') }}</td>

                                            <td><a href="{{ route('email_logs.show', ['logs' => $log['email_id'] ?? "" ]) }}"
                                                class="btn btn-sm btn-outline-info"><i class="fas fa-eye"></i></a>
                                        </td>

                                        </tr>
                                    @endforeach
                                </tbody>
                            </table>

                        </div>
                        <div class="pagination-container mt-1">
                            <nav aria-label="Page navigation example">
                                <ul class="pagination">
                                    @php

                                        $page_counts = $logs->lastPage();

                                        $currentPage = $logs->currentPage();
                                        $lastPage = $logs->lastPage();
                                    @endphp
                                    <li class="page-item {{ $currentPage == 1 ? 'disabled' : '' }}">
                                        <a class="page-link" href="{{ $logs->previousPageUrl() }}">Previous</a>
                                    </li>
                                    @if ($page_counts <= 5)

                                        @for ($i = 1; $i <= $page_counts; $i++)
                                            <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                                <a class="page-link" href="{{ $logs->url($i) }}">{{ $i }}</a>
                                            </li>
                                        @endfor
                                    @else
                                        @for ($i = 1; $i <= 2; $i++)
                                            <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                                <a class="page-link" href="{{ $logs->url($i) }}">{{ $i }}</a>
                                            </li>
                                        @endfor
                                        @if ($currentPage > 2)
                                            <li class="page-item disabled"><span class="page-link">...</span></li>
                                        @endif
                                        @for ($i = max(3, $currentPage - 1); $i <= min($lastPage - 2, $currentPage + 1); $i++)
                                            <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                                <a class="page-link" href="{{ $logs->url($i) }}">{{ $i }}</a>
                                            </li>
                                        @endfor
                                        @if ($currentPage < $lastPage - 3)
                                            <li class="page-item disabled"><span class="page-link">...</span></li>
                                        @endif
                                        @for ($i = $lastPage - 1; $i <= $lastPage; $i++)
                                            <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                                <a class="page-link" href="{{ $logs->url($i) }}">{{ $i }}</a>
                                            </li>
                                        @endfor
                                    @endif
                                    <li class="page-item {{ $currentPage == $lastPage ? 'disabled' : '' }}">
                                        <a class="page-link" href="{{ $logs->nextPageUrl() }}">Next</a>
                                    </li>
                                </ul>

                            </nav>
                        </div>


                        <!-- /.card-body -->
                    </div>
                    <!-- /.card -->
                </div>
                <!-- /.col -->
            </div>
            <!-- /.row -->
        </div>
        <!-- /.container-fluid -->
    </section>

    <!-- Include jQuery and Bootstrap JavaScript (if not already included) -->
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>

    <script>
        $(document).ready(function() {
            setTimeout(function() {
                $('#flash-message').alert('close');
            }, 5000); // 5000 milliseconds = 5 seconds
        });
    </script>
   @endsection
