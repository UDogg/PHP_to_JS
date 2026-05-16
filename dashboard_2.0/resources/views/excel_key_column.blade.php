@extends('layout.app', ['pageTitle' => 'Excel Key Column', 'pageHeader' => 'Excel Key Column', 'menu' => 'Excel Key Column', 'subMenu' => 'Excel Key Column'])
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
                        <a href="{{ route('excel_column.index') }}" class="btn btn-dark"><i
                                class="fa-solid fa-arrow-left"></i></a>
                    </div>
                    <div class="card-body">
                        @csrf
                        <div class="card-body">
                            <form action="{{ route('excel_column.store') }}" method="POST">
                                @csrf
                                <div class="card-body">
                                    <div class="form-group">
                                        <div class="row">
                                            <div class="col-md-6">
                                                <label for="enviroment"
                                                    class = "required">Policy Status Column Master</label>
                                                <select name="policystatus_column_master_id" class="form-control" id="">
                                                    <option value="">Select Policy Status Column</option>
                                                    @foreach ($policyStatus as $config)
                                                        <option value="{{ $config->id }}">{{ $config->column_name }}</option>
                                                    @endforeach
                                                </select>
                                            </div>
                                            <div class="col-md-6">
                                                <label for="lob_id" class = "required">Lob</label>
                                                <input type="text" class="form-control" id="lob_id"
                                                    placeholder="Enter Credential Key" name="lob_id"
                                                    value="{{ old('lob_id') }}" required>
                                            </div>
                                            <div class="col-md-6">
                                                <label for="excel_column_name" class = "required">Excel Column Name</label>
                                                <input type="text" class="form-control" id="excel_column_name"
                                                    placeholder="Enter Credential Key" name="excel_column_name"
                                                    value="{{ old('excel_column_name') }}" required>
                                            </div>
                                            <div class="col-md-6">
                                                <label for="sequence" class = "">Sequence</label>
                                                <input type="sequence" class="form-control" id="sequence"
                                                    placeholder="Enter Credential Value" name="sequence"
                                                    value="{{ old('sequence') }}">
                                            </div>
                                            <div class="col-md-6">
                                                <label for="is_visible" class = "required">Is Visible</label>
                                                <input type="text" class="form-control" id="is_visible"
                                                    placeholder="Enter is_visible" name="is_visible"
                                                    value="{{ old('is_visible') }}" required>
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
                            toastr.success('Credential Created Successfully')
                            setTimeout(function() {
                                location.reload()
                            }, 1500)
                        } else if (data.status == 503) {
                            toastr.error(data.message)
                        } else {
                            toastr.error(
                                'Error In Creating The Credential Please Try Again After Some Time')
                            setTimeout(function() {
                                location.reload()
                            }, 1500)
                        }
                    })
                })
            })
        </script>
    @endsection
