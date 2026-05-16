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
                    <a  href="{{ route('session.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('session.update',$session) }}" method="POST">
                        @csrf @method('PUT')
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">

                                    <div class="col-md-6">
                                        <label for="session_time" class = "required">Session Time</label>
                                        <input type="time" class="form-control" id="session_time"
                                            placeholder="Session Time" name="session_time" value="{{ $session->session_time }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="session_content" class = "required">Session Content</label>
                                        <input type="session_content" class="form-control" id="session_content"
                                            placeholder="Enter Session Content" name="session_content" value="{{ $session->session_content }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="broker_name" class = "required">Broker Name</label>
                                        <select id="broker_name" name="broker_name" class="form-control" required>

                                            <option value="" {{ old('broker_name') == '' ? 'selected' : '' }}>
                                                Select Broker</option>

                                                @foreach ($brokerNames as $brokerName)
                                                <option value="{{ $brokerName }}"
                                                    {{ old('broker_name', $session->broker_name) == $brokerName ? 'selected' : '' }}>
                                                    {{ $brokerName }}
                                                </option>
                                            @endforeach

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
@endsection

