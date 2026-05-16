@extends('layout.app', ['pageTitle' => 'State Master', 'pageHeader' => 'State Master', 'menu' => 'State Master', 'subMenu' => 'State Master'])
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
                            <a class="btn btn-dark float-right" href="{{ route('state_master.create') }}">ADD <i
                                    class="fa-solid fa-plus"></i></a>
                        </div>
                        <div class="card-body">
                            <table id="example1" class="table table-bordered table-striped">
                                <thead>
                                    <tr>
                                        <th>State Name</th>
                                    </tr>
                                </thead>
                                <tbody>
                                    @foreach ($state_master as $data)
                                        <tr>

                                            <td>{{ $data->state_name }}</td>

                                            <td>
                                                <form action="{{ route('state_master.destroy', $data->state_id) }}"
                                                    method="post"
                                                    onsubmit="return confirm('Are you sure to delete this pincode..?')"
                                                    style="display:inline-block; margin-right: 5px;">
                                                    @csrf
                                                    @method('DELETE')
                                                    <button type="submit" class="btn btn-sm btn-outline-danger">
                                                        <i class="fa-solid fa-trash"></i>
                                                    </button>
                                                </form>
                                                <a href="{{ route('state_master.edit', $data->state_id) }}"
                                                    class="btn btn-sm btn-outline-info" style="display:inline-block;">
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
