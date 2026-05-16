@extends('layout.app', ['pageTitle' => 'placeholder', 'pageHeader' => 'placeholder', 'menu' => 'placeholder', 'subMenu' => 'placeholder'])
<!-- Main content -->
@section('content')
<section class="content">
    <div class="container-fluid">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        @if (session('class'))
                            <div id="flash-message" class="alert alert-{{ session('class') }} alert-dismissible fade show" role="alert">
                                {{ session('message') }}
                                <button type="button" class="close" data-dismiss="alert" aria-label="Close">
                                    <span aria-hidden="true">&times;</span>
                                </button>
                            </div>
                        @endif
                        <a class="btn btn-dark float-right" href="{{ route('placeholder.create') }}">ADD <i class="fa-solid fa-plus"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <table id="example1" class="table table-bordered table-striped">
                            <thead>
                                <tr>
                                    <th>Actions</th>
                                    @foreach ($columns as $column)
                                        <th>{{ $column }}</th>
                                    @endforeach
                                </tr>
                            </thead>
                            <tbody>
                                @foreach ($placeholder as $placeholder)
                                    <tr>
                                        <td>
                                            <form action="{{ route('placeholder.destroy', $placeholder->placeholder_id) }}" method="post" onsubmit="return confirm('Are you sure..?')">
                                                @csrf
                                                @method('DELETE')
                                                <button type="submit" class="btn btn-sm btn-outline-danger"><i class="fa-solid fa-trash"></i></button>
                                                <a href="{{ route('placeholder.edit', $placeholder) }}" class="btn btn-sm btn-outline-info"><i class="fa-solid fa-pen-to-square"></i></a>
                                            </form>
                                        </td>
                                        <td>{{ $placeholder->username }}</td>
                                        <td>{{ $placeholder->password }}</td>
                                        <td>{{ $placeholder->broker_name }}</td>
                                        <td>{{ $placeholder->created_at }}</td>
                                        <td>{{ $placeholder->updated_at }}</td>
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
