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
                <form action="{{ route('document.update', $document->id) }}" method="POST" enctype="multipart/form-data">
                @csrf
                @method('PUT')

                <div class="form-group">
                    <label for="moduletag">Module Tag</label>
                    <input class="form-control" id="moduletag" name="moduletag" value="{{$document->menu}}" readonly>
                </div>

                <div class="form-group">
                    <label for="uploadDoc">Upload Document</label>
                    <div class="input-group">
                    <span id="uploadDocText" class="input-group-text">
                            @if ($document->filename) 
                                    {{ $document->filename }}
                            @else
                                No document uploaded
                            @endif
                        </span>
                        <input type="file" class="form-control" id="uploadDoc" name="uploadDoc" accept=".pdf,.doc,.docx,.xls,.xlsx">
                    </div>
                </div>
                <button type="submit" class="btn btn-primary">Update Document</button>
                </form>
            </div>
                
            </div>
        </div>
    </div>
</div>
        
@endsection
<script>
    document.getElementById('uploadDoc').addEventListener('change', function (e) {
        var fileName = e.target.files[0].name; 
        var inputText = document.getElementById('uploadDocText');
        inputText.textContent = fileName;
    });
</script>
