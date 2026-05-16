@extends('layout.app', ['pageTitle' => 'Credential', 'pageHeader' => 'Credential', 'menu' => 'Credential', 'subMenu' => 'Credential'])
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
                    <a  href="{{ route('credential.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('credential.store') }}" method="POST">
                        @csrf
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="credential_label" class = "required">Credential Configuration</label>
                                        <input type="text" class="form-control" id="credential_config"
                                            placeholder="Enter Credential Config" name="credential_config" value="" >
                                    </div>
                                </div>
                            </div>
                        <button type="button" class="btn btn-sm btn-secondary add_btn">Add</button>
                        </div>     <div class="card-body">
                    <form action="{{ route('credential.store') }}" method="POST">
                        @csrf
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="credential_label" class = "required">Credential Label</label>
                                        <input type="text" class="form-control" id="credential_label"
                                            placeholder="Enter Credential Key" name="credential_label" value="{{ old('credential_label') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="credential_key" class = "required">Credential Key</label>
                                        <input type="text" class="form-control" id="credential_key"
                                            placeholder="Enter Credential Key" name="credential_key" value="{{ old('credential_key') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="credential_value" class = "required">Credential value</label>
                                        <input type="credential_value" class="form-control" id="credential_value"
                                            placeholder="Enter Credential Value" name="credential_value" value="{{ old('credential_value') }}">
                                    </div>
                                    <div class="col-md-6">
                                        <label for="enviroment" class = "required">Enviroment</label>
                                        <input type="text" class="form-control" id="enviroment"
                                            placeholder="Enter Enviroment" name="enviroment" value="{{ old('enviroment') }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="enviroment" class = "required">Configuration</label>
                                        <select name="configs" class="form-control" id="">
                                            <option value="">Select Config</option>
                                            @foreach($all_configurations as $config)
                                                <option value="{{$config->id}}">{{$config->key}}</option>
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
    <script>
        $(function() {
            $(".add_btn").click(function(){
                var congfig  = $("[name='credential_config']").val();
                var token = $("[name='_token']").val();
                $.post('AddConfig',{_token:token,credential_config:congfig},function(data){

                    if(data.status == 200)
                    {
                        toastr.success('Credential Created Successfully')
                        setTimeout(function(){
                            location.reload()
                        },1500)
                    }
                    else if(data.status == 503)
                    {
                        toastr.error(data.message)
                    }
                    else
                    {
                        toastr.error('Error In Creating The Credential Please Try Again After Some Time')
                        setTimeout(function(){
                            location.reload()
                        },1500)
                    }
                })
            })
        })
    </script>
@endsection
