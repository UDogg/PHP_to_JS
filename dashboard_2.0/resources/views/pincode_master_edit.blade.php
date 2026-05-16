@extends('layout.app', ['pageTitle' => 'Pincode Master', 'pageHeader' => 'Pincode Master', 'menu' => 'Pincode Master', 'subMenu' => 'Pincode Master'])
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
                        <a href="{{ route('pincode_master.index') }}" class="btn btn-dark"><i
                                class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <form action="{{ route('pincode_master.update', $pincode_master->pincode_id) }}" method="POST">
                            @csrf
                            @method('PUT')
                            <div class="card-body">
                                <div class="form-group">
                                    <div class="row">


                                        <div class="col-md-6">
                                            <label for="pincode" class="required">Pincode</label>
                                            <input type="text" class="form-control" id="pincode" name="pincode"
                                                value="{{ old('pincode', $pincode_master->pincode) }}" required>
                                        </div>


                                        <div class="col-md-6">
                                            <label for="city_id">City</label>
                                            <select name="city_id" class="form-control">
                                                <option value="">Select City</option>
                                                @foreach ($city_master as $city)
                                                    <option value="{{ $city->city_id }}"
                                                        {{ old('city_id', $pincode_master->city_id) == $city->city_id ? 'selected' : '' }}>
                                                        {{ $city->city_name }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="state_id">State</label>
                                            <select name="state_id" class="form-control">
                                                <option value="">Select State</option>
                                                @foreach ($state_master as $state)
                                                    <option value="{{ $state->state_id }}"
                                                        {{ old('state_id', $pincode_master->state_id) == $state->state_id ? 'selected' : '' }}>
                                                        {{ $state->state_name }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="country_code" class="required">country_code</label>
                                            <input type="text" class="form-control" id="country_code" name="country_code"
                                                value="{{ old('country_code', $pincode_master->country_code) }}" required>
                                        </div>


                                    </div>
                                </div>
                            </div>
                            <!-- /.card-body -->
                            <div class="card-footer">
                                <button type="submit" class="btn btn-dark">Update</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
        </div>
    </div>
@endsection
