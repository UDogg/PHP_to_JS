@extends('layout.app', ['pageTitle' => 'Menu', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
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
                    <form action="{{ route('menu.update',$menu) }}" method="POST">
                        @csrf @method('PUT')
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">

                                    <div class="col-md-6">
                                        <label for="menu_name" class = "required">Name</label>
                                        <input type="text" class="form-control" id="menu_name"
                                            placeholder="Enter Name" name="menu_name" value="{{ $menu->menu_name }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="menu_link" class = "required">Route Url</label>
                                        <input type="menu_link" class="form-control" id="menu_link"
                                            placeholder="Enter Route Url" name="menu_link"  value="{{ $menu->menu_link }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="menu_slug" class = "required">Menu Slug</label>
                                        <input type="menu_slug" class="form-control" id="menu_slug"
                                            placeholder="Enter slug" name="menu_slug"  disabled value ="{{ $menu->menu_slug }}" required>
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

