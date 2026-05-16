@extends('layout.app', ['pageTitle' => 'marquee', 'pageHeader' => 'marquee', 'menu' => 'marquee', 'subMenu' => 'marquee'])
@section('content')
    <div class="container">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        <a href="{{ route('marquee.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('marquee.update', $data) }}" method="POST" enctype="multipart/form-data">
                            @csrf @method('PUT')
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="usertype" class = "required">usertype</label>
                                            <input type="text" class="form-control" id="usertype"
                                                placeholder="Enter usertype Name" name="usertype"
                                                value="{{ $data->usertype }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="status" class="required">status</label>
                                            <select name="status" class="form-control" required>

                                                <option value="Y">Yes</option>
                                                <option value="N">No</option>
                                            </select>
                                        </div>

                                    </div>
                                </div>
                            </div>
                            <!-- /.card-body -->
                            <div class="card-footer">
                                <button type="submit" class="btn btn-dark">Submit</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
        </div>
    </div>
    <!-- Bootstrap CSS -->
    <link href="https://maxcdn.bootstrapcdn.com/bootstrap/4.5.2/css/bootstrap.min.css" rel="stylesheet">
    <!-- Bootstrap Select CSS -->
    <link href="https://cdnjs.cloudflare.com/ajax/libs/bootstrap-select/1.13.18/css/bootstrap-select.min.css" rel="stylesheet">
    <!-- jQuery -->
    <script src="https://ajax.googleapis.com/ajax/libs/jquery/3.5.1/jquery.min.js"></script>
    <!-- Bootstrap JS -->
    <script src="https://maxcdn.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>
    <!-- Bootstrap Select JS -->
    <script src="https://cdnjs.cloudflare.com/ajax/libs/bootstrap-select/1.13.18/js/bootstrap-select.min.js"></script>
    <script>
        $(document).ready(function() {
            $('.select2').select2({
        closeOnSelect: false
    })
        });
    </script>
@endsection
