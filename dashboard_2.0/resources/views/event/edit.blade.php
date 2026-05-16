@extends('layout.app', ['pageTitle' => 'Event', 'pageHeader' => 'Event', 'menu' => 'Event', 'subMenu' => 'Event'])
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
                        <a href="{{ route('event.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('event.update',['event' => $event->event_id]) }}" method="POST">
                            @csrf @method('PUT')

                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="event_name" class = "required">Event Name</label>
                                            <input type="text" class="form-control" id="event_name"
                                                name="event_name" placeholder="Event Name"
                                                value="{{ $event->event_name }}" required>

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
