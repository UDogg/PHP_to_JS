@extends('layout.app', ['pageTitle' => 'Mis Column View', 'pageHeader' => 'Mis Column View', 'menu' => 'MisColumnView', 'subMenu' => 'MisColumnView']);
<!-- Main content -->
<head>
    <meta name="csrf-token" content="{{ csrf_token() }}">
</head>
@section('content')
    @php
        $user = \Illuminate\Support\Facades\Auth::user();
    @endphp
    <!-- Main content -->
    <section class="content">


        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Mis Column View</h3>
            </div>
            <form method="post" name="mis_column_view" id="misForm" enctype="multipart/form-data"
            action="miscolumnview/store">
            <input type="hidden" id="edit_id" name="edit_id">

                @csrf
                <div class="card-body">
                    <div class="row">
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="mongo_key">Mongo Key</label>
                                <select type="text" class="form-control" id="mongo_key" name="mongo_key" required>
                           
                                </select>
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Existing Value</label>
                                <input type="text" maxlength="50" name="existing_value" class="form-control"
                                    id="existing_value" placeholder="Enter Existing Value" required>
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">New value</label>
                                <input type="text" maxlength="50" name="new_value" class="form-control"
                                    id="new_value" placeholder="Enter New Value">
                            </div>
                        </div>
                    </div>
                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtn">Submit</button>
                </div>
            </form>

            <div class="card mt-3">
                <div class="card-header">
                    <h3 class="card-title">Existing Records</h3>
                </div>
            
                <div class="card-body table-responsive">
                    <table class="table table-bordered table-hover" id="mis_table">
                        <thead>
                            <tr>
                                <th>ID</th>
                                <th>Mongo Key</th>
                                <th>Existing Value</th>
                                <th>New Value</th>
                                <th>Actions</th>
                            </tr>
                        </thead>
            
                        <tbody>
                            @foreach($items as $item)
                                <tr>
                                    <td>{{ $item->id }}</td>
                                    <td>{{ $item->mongo_key }}</td>
                                    <td>{{ $item->existing_value }}</td>
                                    <td>{{ $item->new_value }}</td>
            
                                    <td>
                                        <button class="btn btn-sm btn-info editBtn"
                                            data-item='@json($item)'>
                                            Edit
                                        </button>
            
                                        <form action="miscolumnview/delete/{{ $item->id }}"
                                              method="POST"
                                              style="display:inline-block">
                                            @csrf
                                            @method('DELETE')
            
                                            <button type="submit"
                                                    class="btn btn-sm btn-danger deleteBtn">
                                                Delete
                                            </button>
                                        </form>
            
                                    </td>
                                </tr>
                            @endforeach
                        </tbody>
                    </table>
                </div>
            </div>

        </div>

    </section>
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="{{ asset('Js/miscolumnview.js') }}"></script>

@endsection
