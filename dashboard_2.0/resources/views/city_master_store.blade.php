@extends('layout.app', ['pageTitle' => 'City Master', 'pageHeader' => 'City Master', 'menu' => 'City Master', 'subMenu' => 'City Master'])
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
                            <form action="{{ route('city_master.store') }}" method="POST">
                                @csrf
                                <div class="card-body">
                                    <div class="form-group">
                                        <div class="row">
                                            <div class="col-md-6">
                                                <label for="city_name" class = "required">City Name</label>
                                                <input type="pincode" class="form-control" id="pincode"
                                                    placeholder="Enter City Name" name="city_name"
                                                    value="{{ old('city_name') }}" required>
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
