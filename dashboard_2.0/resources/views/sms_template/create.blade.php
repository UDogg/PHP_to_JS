@extends('layout.app', ['pageTitle' => 'Session Time', 'pageHeader' => 'Session Time', 'menu' => 'Session Time', 'subMenu' => 'Session'])
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
                        <a href="{{ route('sms_template.index') }}" class="btn btn-dark"><i
                                class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('sms_template.store') }}" method="POST">
                            @csrf
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        {{-- <div class="form-group row"
                                            style="display: flex; flex-direction: row; align-items: center;">
                                            <label for="title" class="col-sm-2 col-form-label required">Title</label>
                                            <div class="col-sm-10">
                                                <input type="text" name="title" class="form-control" id="title"
                                                    placeholder="Title" value="{{ old('title') }}">
                                                @error('title')
                                                    <span class="text-danger">{{ $message }}</span>
                                                @enderror
                                            </div>
                                        </div> --}}
                                        <div class="col-md-6">
                                            <label for="title" class = "required">title</label>
                                            <input type="text" class="form-control" id="title"
                                                name="title" placeholder="title"
                                                value="{{ old('title') }}" required>

                                        </div>
                                        {{-- <div class="form-group row"
                                            style="display: flex; flex-direction: row; align-items: center;">
                                            <label for="content" class="col-sm-2 col-form-label required">Content</label>
                                            <div class="col-sm-10">
                                                <input type="text" name="content" class="form-control" id="content"
                                                    placeholder="content" value="{{ old('content') }}">
                                                @error('content')
                                                    <span class="text-danger">{{ $message }}</span>
                                                @enderror
                                            </div>
                                        </div> --}}
                                        <div class="col-md-6">
                                            <label for="content" class = "required">content</label>
                                            <input type="text" class="form-control" id="content"
                                                name="content" placeholder="content"
                                                value="{{ old('content') }}" required>

                                        </div>
                                        <div class="col-md-6">
                                            <label for="status" class="required">Status</label>
                                            <div class="col-sm-2">
                                                <div class="form-check form-switch">
                                                    <input class="form-check-input" type="checkbox" role="switch"
                                                        id="status" name="status" value="on"
                                                        {{ old('status') == 'off' ? '' : 'checked' }}>
                                                </div>

                                                @error('status')
                                                    <span class="text-danger">{{ $message }}</span>
                                                @enderror
                                            </div>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="content" class = "required">Dlt id</label>
                                            <input type="text" class="form-control" id="dlt_id"
                                                name="dlt_id" placeholder="dlt_id"
                                                value="{{ old('dlt_id') }}" required>

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
