@extends('layout.app', ['pageTitle' => 'placeholder', 'pageHeader' => 'placeholder', 'menu' => 'placeholder', 'subMenu' => 'placeholder'])
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
                        <a href="{{ route('sms_template.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('sms_template.update',['sms_template' => $sms->template_id]) }}" method="POST">
                            @csrf @method('PUT')

                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        {{-- <div class="col-md-6">
                                            <label for="username" class = "required">Username</label>
                                            <input type="text" class="form-control" id="username"
                                                placeholder="Enter Username" name="username"
                                                value="{{ $placeholder->username }}" required>
                                        </div> --}}
                                        <div class="col-md-6">
                                            <label for="title" class = "required">title</label>
                                            <input type="text" class="form-control" id="title"
                                                name="title" placeholder="title"
                                                value="{{ $sms->title }}" required>

                                        </div>
                                        <div class="col-md-6">
                                            <label for="content" class = "required">content</label>
                                            <input type="text" class="form-control" id="content"
                                                placeholder="Enter content" name="content"
                                                value="{{ $sms->content }}" required>
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
                                            <label for="dlt_id">Dlt id</label>
                                            <input type="text" class="form-control" id="dlt_id"
                                                placeholder="Enter dlt_id" name="dlt_id"
                                                value="{{ $sms->dlt_id }}">
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
