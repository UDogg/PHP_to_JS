@extends('layout.app', ['pageTitle' => 'State Master', 'pageHeader' => 'State Master', 'menu' => 'State Master', 'subMenu' => 'State Master'])
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
                        <form action="{{ route('state_master.update', $state_master->state_id) }}" method="POST">
                            @csrf
                            @method('PUT')
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">
                                        <div class="col-md-6">
                                            <label for="state_name" class="required">State Name</label>
                                            <input type="state_name" class="form-control" id="state_name" name="state_name"
                                                value="{{ old('state_name', $state_master->state_name) }}" required>
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
