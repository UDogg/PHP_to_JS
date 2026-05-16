@extends('layout.app', ['pageTitle' => 'Broker', 'pageHeader' => 'Broker', 'menu' => 'Broker', 'subMenu' => 'Broker'])
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
                        <a class="btn btn-dark float-right" href="{{ route('broker.create') }}">ADD <i class="fa-solid fa-plus"></i></a>
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
                                @foreach ($broker as $broker)
                                    <tr>
                                        <td>

                                            <form action="{{ route('broker.destroy', $broker) }}" method="post" onsubmit="return confirm('Are you sure..?')">
                                                @csrf
                                                @method('DELETE')
                                                {{-- <button type="submit" class="btn btn-sm btn-outline-danger"><i class="fa-solid fa-trash"></i></button> --}}
                                                <a href="{{ route('broker.show', ['broker' => $broker->broker_id]) }}" class="btn btn-sm btn-outline-info"><i class="fas fa-eye"></i></a>
                                                <a href="{{ route('broker.edit', $broker) }}" class="btn btn-sm btn-outline-info"><i class="fas fa-pencil"></i></a>
                                            </form>

                                        </td>
                                        <td>{{ $broker->broker_name }}</td>
                                        <td>{{ $broker->category }}</td>
                                        <td>{{ $broker->cin_no }}</td>
                                        <td>{{ $broker->address }}</td>
                                        <td>{{ $broker->contact_no }}</td>
                                        <td>{{ $broker->email }}</td>
                                        <td>{{ $broker->irdia_registration_no }}</td>
                                        <td>{{ $broker->favicon_icon }}</td>
                                        <td>{{ $broker->logo }}</td>
                                        <td>{{ $broker->sign_in_option }}</td>
                                        <td>{{ $broker->status }}</td>
                                        <td>{{ $broker->captacha_configure }}</td>
                                        <td>{{ $broker->is_email }}</td>
                                        <td>{{ $broker->is_sms }}</td>
                                        <td>{{ $broker->default_otp }}</td>
                                        <td>{{ $broker->master_otp }}</td>
                                        <td>{{$broker->front_logo}}</td>
                                        <td>{{$broker->marquee}}</td>
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
