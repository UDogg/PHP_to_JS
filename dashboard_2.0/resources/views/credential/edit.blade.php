@extends('layout.app', ['pageTitle' => 'Menu', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
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
                    <form action="{{ route('credential.update',$credential) }}" method="POST">
                        @csrf @method('PUT')
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="credential_label" class = "required">Credential Configuration</label>
                                        <select class="form-control" id="credential_config" name="credential_config">
                                            <option value="">Select Credential Configuration</option>
                                            @foreach ($all_configurations as $config)
                                                <option value="{{ $config->id }}" 
                                                    {{ old('credential_config', $credential->configuration) == $config->id ? 'selected' : '' }}>
                                                    {{ $config->key }}
                                                </option>
                                            @endforeach
                                        </select>
                                    </div>

                                    <div class="col-md-6">
                                        <label for="credential_label" class = "required">Credential Label</label>
                                        <input type="text" class="form-control" id="credential_label"
                                            placeholder="Enter Credential Label" name="credential_label" value="{{ $credential->credential_label }}" required>
                                    </div>

                                    <div class="col-md-6">
                                        <label for="credential_key" class = "required">Credential Key</label>
                                        <input type="text" class="form-control" id="credential_key"
                                            placeholder="Enter Credential Key" name="credential_key" value="{{ $credential->credential_key }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="credential_value" class = "required">Credential value</label>
                                        <input type="text" class="form-control" id="credential_value"
                                            placeholder="Enter Credential Value" name="credential_value"  value="{{ credential_decrypt($credential->credential_value) }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="Enviroment" class = "required">Enviroment</label>
                                        <input type="text" class="form-control" id="enviroment"
                                            placeholder="Enter Enviroment" name="enviroment"  value="{{ credential_decrypt($credential->enviroment) }}">
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

