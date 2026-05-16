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
                        <a href="{{ route('broker.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('broker.store') }}" method="POST" enctype="multipart/form-data">
                            @csrf
                            <div class="card-header">
                                <h3>{{ $broker->broker_name }}</h3>
                            </div>
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">
                                        <div class="col-md-6">
                                            <p><strong>Broker Name:</strong> {{ $broker->broker_name }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Category:</strong> {{ $broker->category }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>IRDAI Registration No:</strong> {{ $broker->irdia_registration_no }}
                                            </p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Email:</strong> {{ $broker->email }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Contact No:</strong> {{ $broker->contact_no }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>CIN No:</strong> {{ $broker->cin_no }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Address:</strong> {{ $broker->address }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Sign In Option:</strong> {{ $broker->sign_in_option }}</p>
                                        </div>

                                        <div class="col-md-6">
                                            <p><strong>Logo:</strong></p>

                                            <img src="{{ Storage::url($broker->logo) }}" alt="Broker Logo"
                                                style="max-width: 100px;">
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Favicon Icon:</strong></p>
                                            <img src="{{ Storage::url($broker->favicon_icon) }}" alt="Broker Favicon Icon"
                                                style="max-width: 100px;">
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Captacha Configure:</strong> {{ $broker->captacha_configure }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Is Email:</strong> {{ $broker->is_email }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Is Sms:</strong> {{ $broker->is_sms }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Default Otp:</strong> {{ $broker->default_otp }}</p>
                                        </div>
                                        <div class="col-md-6">
                                            <p><strong>Master Otp:</strong> {{ $broker->master_otp }}</p>
                                        </div>
                                    </div>
                                </div>
                            </div>
                            <div class="card-footer">
                                <a href="{{ route('broker.index') }}" class="btn btn-primary">Back to List</a>
                                <a href="{{ route('broker.edit', $broker->broker_id) }}" class="btn btn-success">Edit</a>
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
