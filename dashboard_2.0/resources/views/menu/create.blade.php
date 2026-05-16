@extends('layout.app', ['pageTitle' => 'Menu', 'pageHeader' => 'menu', 'menu' => 'menu', 'subMenu' => 'User'])
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
                    <a  href="{{ route('menu.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('menu.store') }}" method="POST">
                        @csrf
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">

                                    <div class="col-md-6">
                                        <label for="menu_name" class = "required">Name</label>
                                        <input type="text" class="form-control" id="menu_name"
                                            placeholder="Enter Name" name="menu_name" value="{{ old('menu_name') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="menu_link" class = "required">Route Url</label>
                                        <input type="menu_name" class="form-control" id="menu_link"
                                            placeholder="Enter Route Url" name="menu_link" value="{{ old('menu_link') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="menu_slug" class = "required">Slug</label>
                                        <input type="menu_slug" class="form-control" id="menu_slug"
                                            placeholder="Enter slug" name="menu_slug" value="{{ old('menu_slug') }}" required>
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
@endsection