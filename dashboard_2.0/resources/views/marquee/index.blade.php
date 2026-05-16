@extends('layout.app', ['pageTitle' => 'marquee', 'pageHeader' => 'marquee', 'menu' => 'marquee', 'subMenu' => 'marquee'])
<!-- Main content -->
@section('content')
<section class="content">
    <div class="container-fluid">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        <a class="btn btn-dark float-right" href="{{ route('marquee.create') }}">ADD <i class="fa-solid fa-plus"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <table id="example1" class="table table-bordered table-striped">
                            <thead>
                                <tr>
                                    <th>Sr.no</th>
                                    <th>Actions</th>
                                    <th>usertype</th>
                                    <th>status</th>
                                </tr>
                            </thead>
                            <tbody>
                                @foreach ($datas as $data)
                                    <tr>
                                        <td>{{ $data->id }}</td>
                                        <td>
                                            <form action="{{ route('marquee.destroy', $data->id) }}" method="post" onsubmit="return confirm('Are you sure..?')">
                                                @csrf
                                                @method('DELETE')
                                                <button type="submit" class="btn btn-sm btn-outline-danger"><i class="fa-solid fa-trash"></i></button>
                                                <a href="{{ route('marquee.edit', $data) }}" class="btn btn-sm btn-outline-info"><i class="fa-solid fa-pen-to-square"></i></a>
                                            </form>
                                        </td>
                                        <td>{{ $data->usertype }}</td>
                                        <td>{{ $data->status }}</td>
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

<!-- <script>
    $(document).ready(function() {
        setTimeout(function() {
            $('#flash-message').alert('close');
        }, 5000); // 5000 milliseconds = 5 seconds
    });
</script> -->
@endsection
