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
                        <a href="{{ route('placeholder.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('placeholder.update', $placeholder->placeholder_id) }}" method="POST">
                            @csrf @method('PUT')

                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="username" class = "required">Username</label>
                                            <input type="text" class="form-control" id="username"
                                                placeholder="Enter Username" name="username"
                                                value="{{ $placeholder->username }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="password" class = "required">Password</label>
                                            <input type="text" class="form-control" id="password"
                                                placeholder="Enter password" name="password"
                                                value="{{ $placeholder->password }}" required>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="broker_name" class = "required">Broker Name</label>
                                            <select id="broker_name" name="broker_name" class="form-control" required>

                                                <option value="" {{ old('broker_name') == '' ? 'selected' : '' }}>
                                                    </option>

                                                @foreach ($brokerNames as $brokerName)
                                                    <option value="{{ $brokerName }}"
                                                        {{ old('broker_name', $placeholder->broker_name) == $brokerName ? 'selected' : '' }}>
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
