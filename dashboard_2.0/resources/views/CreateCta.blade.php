@extends('layout.app', ['pageTitle' => 'CTA', 'pageHeader' => 'CTA', 'menu' => 'CTA', 'subMenu' => 'CTA'])
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
                        <form action="{{ route('placeholder.store') }}" method="POST">
                            @csrf
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="username" class = "required">Username</label>
                                            <input type="text" class="form-control" id="username"
                                                placeholder="Enter Username" name="username"
                                                value="{{ old('username') }}" required>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="stageMasterData" class = "required">Stage Master</label>
                                            <select id="stageMasterData" name="stageMasterData" class="form-control" required>
                                                <option value="" {{ old('stageMasterData') == '' ? 'selected' : '' }}>
                                                    Select Stage Master
                                                </option>
                                                @foreach ($stageMasterData as $stageMaster)
                                                    <option value="{{ $stageMaster->id }}" {{ old('stageMasterData') == $stageMaster->id ? 'selected' : '' }}>
                                                        {{ $stageMaster->stage_name }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>
                                        <div class="col-md-6">
                                            <label for="lobMasterData" class = "required">Lob Master</label>
                                            <select id="lobMasterData" name="lobMasterData" class="form-control" required>
                                                <option value="" {{ old('lobMasterData') == '' ? 'selected' : '' }}>
                                                    Select Lob Master
                                                </option>
                                                @foreach ($lobMasterData as $lobMaster)
                                                    <option value="{{ $lobMasterData->id }}" {{ old('lobMasterData') == $lobMasterData->id ? 'selected' : '' }}>
                                                        {{ $lobMasterData->stage_name }}
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
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
