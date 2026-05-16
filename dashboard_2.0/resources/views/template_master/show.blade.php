@extends('layout.app', ['pageTitle' => 'Broker', 'pageHeader' => 'Broker', 'menu' => 'Broker', 'subMenu' => 'Broker'])
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
                        <a href="{{ route('template.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('template.store') }}" method="POST" enctype="multipart/form-data">
                            @csrf
                            <div class="card-header">

                            </div>
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">
                                        <div class="col-md-6">
                                            <p><strong>Title:</strong> {{ $template->title }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>DLT ID:</strong> {{ $template->dlt_id }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Communication Type:</strong> {{ $template->communication_type }}
                                            </p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Event:</strong> {{ $template->event }}
                                            </p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Content:</strong> {{ $template->content }}</p>
                                        </div>
                                        {{-- <div class="col-md-6">
                                            <p><strong>Email Content:</strong> {{ $template->sms_content }}</p>
                                        </div> --}}
                                        <div class="col-md-6">
                                            <p><strong>Status:</strong> {{ $template->status }}</p>
                                        </div>

                                    </div>
                                </div>
                            </div>
                            <div class="card-footer">
                                <a href="{{ route('template.index') }}" class="btn btn-primary">Back to List</a>
                                <a href="{{ route('template.edit', $template->template_id) }}" class="btn btn-success">Edit</a>
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
