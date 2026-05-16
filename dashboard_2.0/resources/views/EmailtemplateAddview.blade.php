@extends('layout.app', ['pageTitle' => 'Email-Template', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
<!-- Main content -->
<style>
    .w-5 {
        display: none;
    }

    .pagination-class {
        height: 300px;
        display: flex;
        justify-content: center;
        margin-top: 20px;
    }
</style>

@section('content')
<section class="content">
    <div class="container-fluid">
        <div class="row">
            <div class="col-12">
                <div class="card">  
                    <div class="card-header">
                        <div class="d-flex justify-content-between align-items-center mb-3">
                            <form action="{{ route('email-template.search') }}" method="POST" class="d-flex">
                                @csrf
                                <input type="text" name="search" placeholder="search by stage,subject,body..." class="form-control mr-2" />
                                <button type="submit" class="btn btn-dark ml-2">Submit</button>
                            </form>
                            <a class="btn btn-dark ml-3" href="{{ route('Email-template-add') }}">
                            ADD <i class="fa-solid fa-plus"></i>
                            </a>
                        </div>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <table id="example1" class="table table-bordered table-striped">
                            <thead>
                                <tr>
                                    <th>Actions</th>
                                    <th>Stage</th>
                                    <th>Subject</th>
                                    <th>body</th>
                                    {{-- @foreach ($columns as $column)
                                        <th>{{ $column }}</th>
                                    @endforeach --}}
                                </tr>
                            </thead>
                            <tbody>
                                @foreach ($EmailViews as $info)
                                    <tr>
                                        <td>
                                            <form action="{{ route('email-templates.delete', $info->id) }}" method="post" >
                                                @csrf
                                                @method('DELETE')
                                                <button type="submit" class="btn btn-sm btn-outline-danger"><i class="fa-solid fa-trash"></i></button>
                                            </form>
                                            <a href="{{ route('email-templates.update', $info->id) }}" class="btn btn-sm btn-outline-info"><i class="fa-solid fa-pen-to-square"></i></a>
                                        </td>
                                        <td>{{ $info->stage}}</td>
                                        <td>{{ $info->subject}}</td>
                                        <td>{{ $info->body}}</td>
                                        {{-- <td>{{ $session->created_at }}</td>
                                        <td>{{ $session->updated_at }}</td> --}}
                                    </tr>
                                @endforeach
                            </tbody>
                        </table>
                        <br/>

<div class="pagination-class">      
    {{ $EmailViews->links() }}
</div>

{{-- <div class="text-center">
    {{ $EmailViews->links() }}
</div> --}}
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
