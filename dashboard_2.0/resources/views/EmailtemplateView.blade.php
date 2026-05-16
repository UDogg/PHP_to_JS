@extends('layout.app', ['pageTitle' => 'Add Email Template', 'pageHeader' => 'Session Time', 'menu' => 'Session Time', 'subMenu' => 'Session'])
@section('content')
    <div class="container">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        <a href="{{ route('Email-Template-Index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('Email-template-store') }}" method="POST">
                            @csrf
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="session_time" class = "required">Stage</label>
                                            <input type="text" class="form-control" name="stage"/>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="session_content" class = "required">Subject</label>
                                            <textarea class="form-control" name="subject" ></textarea>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="broker_name" class = "required">body</label>
                                            <textarea class="form-control" name="body" ></textarea>
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
