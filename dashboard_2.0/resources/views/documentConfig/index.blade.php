@extends('layout.app', ['pageTitle' => 'DocumentConfig', 'pageHeader' => 'DocumentConfig', 'menu' => 'DocumentConfig', 'subMenu' => 'DocumentConfig'])
@section('content')
<div class="container">
    <div class="row">
        <div class="col-12">
            <div class="card">
                <div class="card-header">
                    @if(session('message'))
                        <div class="alert alert-{{ session('class') }}">
                            {{ session('message') }}
                        </div>
                    @endif
                    <a  href="#" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('uploadDocument' )}}" method="POST" enctype="multipart/form-data">
                        @csrf
                        <div class="card-body">
                            <div class="form-group">
                                <div class="row">
                                  <div class="col-md-6">
                                        <label for="moduletag" class="required">Module Tag</label>
                                        <select class="form-control" id="moduletag" name="moduletag" required>
                                            <option value="">Select Module</option>
                                            @foreach ($modules as $module)
                                                <option value="{{ $module->id }}">{{ $module->menu }}</option>
                                            @endforeach
                                        </select>
                                        @error('moduletag')
                                            <span class="invalid-feedback d-inline">{{ $message }}</span>
                                        @enderror
                                    </div>

                                    <div class="col-md-6">
                                        <label for="uploadDoc" class="required">Upload Document</label>
                                        <input type="file" class="form-control" id="uploadDoc" name="uploadDoc" accept=".pdf,.doc,.docx,.xls,.xlsx" required>
                                        @error('uploadDoc')
                                            <span class="invalid-feedback d-inline">{{ $message }}</span>
                                        @enderror
                                    </div>

                                </div>

                            </div>
                        </div>
                        <!-- /.card-body -->
                        <div class="card-footer">
                            <button type="submit" class="btn btn-dark" name="sb_btn">Submit</button>
                        </div>
                    </form>
                </div>
                <div class="card-body">
                    <table id="example1" class="table table-bordered table-striped">
                        <thead>
                            <tr>
                                <th>Module Tag</th>
                                <th>Document Name</th>
                                <th>Action</th>
                            </tr>
                        </thead>
                         <tbody>
                            @foreach ($modules as $document)
                                <tr>
                                    <td>{{ $document->menu }}</td>
                                    <td>{{ $document->filename }}</td>
                                    <td>
                                    <a href="{{ route('downloadDocument', $document->id) }}" class="btn btn-dark btn-sm">
                                        Download
                                    </a>
                                    <a href="{{ route('document.edit', $document->id) }}" class="btn btn-dark btn-sm">
                                        Edit
                                    </a>
                                    </td>
                                </tr>
                            @endforeach
                        </tbody>
                    </table>
                </div>
            </div>
        </div>
    </div>
</div>

@endsection
