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
                        {{-- <a href="{{ route('pincode_master.show') }}" class="btn btn-dark"><i
                                class="fa-solid fa-arrow-left"></i></a> --}}
                    </div>
                    <div class="card-body">
                        @csrf
                        <div class="card-body">
                            <form action="{{ route('pincode_master.store') }}" method="POST">
                                @csrf
                                <div class="card-body">
                                    <div class="form-group">
                                        <div class="row">
                                            <div class="col-md-6">
                                                <label for="pincode" class = "required">Pincode</label>
                                                <input type="pincode" class="form-control" id="pincode"
                                                    placeholder="Enter Pincode" name="pincode" value="{{ old('pincode') }}"
                                                    required>
                                            </div>

                                            <div class="col-md-6">
                                                <label for="city_id" class="required">City</label>
                                                <select name="city_id" class="form-control" id="city_id" required>
                                                    <option value="">Select City</option>
                                                    @foreach ($city_master as $city)
                                                        <option value="{{ $city->city_id }}"
                                                            {{ old('city_id') == $city->city_id ? 'selected' : '' }}>
                                                            {{ $city->city_name }}
                                                        </option>
                                                    @endforeach
                                                </select>
                                            </div>

                                            <div class="col-md-6">
                                                <label for="state_id" class="required">State</label>
                                                <select name="state_id" class="form-control" id="state_id" required>
                                                    <option value="">Select State</option>
                                                    @foreach ($state_master as $state)
                                                        <option value="{{ $state->state_id }}"
                                                            {{ old('state_id') == $state->state_id ? 'selected' : '' }}>
                                                            {{ $state->state_name }}
                                                        </option>
                                                    @endforeach
                                                </select>
                                            </div>


                                            <div class="col-md-6">
                                                <label for="country_code" class = "required">Country Code</label>
                                                <input type="country_code" class="form-control" id="country_code"
                                                    placeholder="Enter Country Code" name="country_code" required>
                                            </div>
                                        </div>
                                    </div>
                                </div>
                                <div class="card-footer">
                                    <button type="submit" class="btn btn-dark">Submit</button>
                                </div>
                            </form>
                        </div>
                    </div>
                </div>
            </div>
        </div>
        <script>
            $(function() {
                $(".add_btn").click(function() {
                    var congfig = $("[name='credential_config']").val();
                    var token = $("[name='_token']").val();
                    $.post('AddConfig', {
                        _token: token,
                        credential_config: congfig
                    }, function(data) {

                        if (data.status == 200) {
                            toastr.success('Pincode Created Successfully')
                            setTimeout(function() {
                                location.reload()
                            }, 1500)
                        } else if (data.status == 503) {
                            toastr.error(data.message)
                        } else {
                            toastr.error(
                                'Error In Creating The Pincode Please Try Again After Some Time')
                            setTimeout(function() {
                                location.reload()
                            }, 1500)
                        }
                    })
                })
            })
        </script>
    @endsection
