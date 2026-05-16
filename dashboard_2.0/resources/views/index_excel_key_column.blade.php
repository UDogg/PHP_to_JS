@extends('layout.app', ['pageTitle' => 'Excel Column', 'pageHeader' => 'Excel Column', 'menu' => 'Excel Column', 'subMenu' => 'Excel Column'])
<!-- Main content -->
@section('content')
    <section class="content">
        <div class="container-fluid">
            <div class="row">
                <div class="col-12">
                    <div class="card">
                        <div class="card-header">
                            @if (session('class'))
                                <div id="flash-message" class="alert alert-{{ session('class') }} alert-dismissible fade show"
                                    role="alert">
                                    {{ session('message') }}
                                    <button type="button" class="close" data-dismiss="alert" aria-label="Close">
                                        <span aria-hidden="true">&times;</span>
                                    </button>
                                </div>
                            @endif
                            <a class="btn btn-dark float-right" href="{{ route('excel_column.create') }}">ADD <i
                                    class="fa-solid fa-plus"></i></a>
                        </div>
                        <div class="card-body">
                            <table id="example1" class="table table-bordered table-striped">
                                <thead>
                                    <tr>
                                        <th>Policy Status Column Master</th>
                                        <th>Excel Column Name</th>
                                        <th>Sequence</th>
                                        <th>Is Visible</th>
                                        <th>Lob</th>
                                        <th>Actions</th>
                                    </tr>
                                </thead>
                                <tbody>
                                    @foreach ($column as $log)
                                        <tr>

                                            <td>{{ $log->policy_status_name }}</td>
                                            <td>{{ $log->excel_column_name }}</td>
                                            <td>{{ $log->sequence }}</td>
                                            <td>{{ $log->is_visible }}</td>
                                            <td>{{ $log->lob_id }}</td>
                                            <td>
                                                <form
                                                    action="{{ route('excel_column.destroy', $log->excel_key_master_id) }}"
                                                    method="post" onsubmit="return confirm('Are you sure..?')">
                                                    @csrf
                                                    @method('DELETE')
                                                    <button type="submit" class="btn btn-sm btn-outline-danger"><i
                                                            class="fa-solid fa-trash"></i></button>
                                                </form>
                                                <a href="{{ route('excel_column.edit', $log->excel_key_master_id) }}"
                                                    class="btn btn-sm btn-outline-info">
                                                    <i class="fa-solid fa-pen-to-square"></i>
                                                </a>
                                            </td>
                                        </tr>
                                    @endforeach
                                </tbody>
                            </table>
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
