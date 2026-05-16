@extends('layout.app', ['pageTitle' => 'City Master', 'pageHeader' => 'City Master', 'menu' => 'City Master', 'subMenu' => 'City Master'])
@section('content')
    <div class="container">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        @if ($errors->any())
                            <div class="alert alert-danger">
                                <ul class="list">
                                    @foreach ($errors->all() as $error)
                                        <li>{{ $error }}</li>
                                    @endforeach
                                </ul>
                            </div>
                        @endif
                        {{-- <a href="{{ route('city_master.show') }}" class="btn btn-dark"><i
                                class="fa-solid fa-arrow-left"></i></a> --}}
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('city_master.update', $city_master->city_id) }}" method="POST">
                            @csrf
                            @method('PUT')
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">
                                        <div class="col-md-6">
                                            <label for="city_name" class="required">City Name</label>
                                            <input type="text" class="form-control" id="city_name" name="city_name"
                                                value="{{ old('city_name', $city_master->city_name) }}" required>
                                        </div>
                                    </div>
                                </div>
                            </div>
                            <!-- /.card-body -->
                            <div class="card-footer">
                                <button type="submit" class="btn btn-dark">Update</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
        </div>
    </div>
@endsection
