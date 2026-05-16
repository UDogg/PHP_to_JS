@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <section class="content">
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Key utility</h3>
            </div>
            <div class="card-body">
                <form method="post" name="key_utility_frm" action="{{route('KeyUtility.store')}}">
                    @csrf
                    <input type="hidden" name="update_mode">
                    <div class="row">
                        <div class="col-sm-12">
                            <div class="form-group">
                                <label for="exampleInputEmail1">Name</label>
                                <input type="text" class="form-control" name="key_name" id="" value="" placeholder="Enter The Common Name Or Key Form Multiple Data ">
                            </div>
                        </div>
                        @foreach($lobs as $lob_val)
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="exampleInputEmail1">{{$lob_val->lob_name}}</label>
                                <select name="columns{{$lob_val->id}}[]" id="columns{{$lob_val->id}}" multiple="" data-placeholder="please select values" class="select2 form-control" 
style="width: 100%;">
                                    <option value="">Select</option>
                                    @foreach($columns as $column)
                                        @if($lob_val->id == $column->lob)
                                            <option value="{{$column->id}}">{{$column->column_name}}</option>

                                            @if(isset($selected_columns[$lob_val->id]) && in_array($column->id, $selected_columns[$lob_val->id])) 
                                                selected >
                                            @endif 
                                            {{-- style="color: black;">
                                            {{$column->column_name}} --}}
                                        </option>
                                    @endif
                                    @endforeach
                            </select>
                            </div>
                        </div>
                        @endforeach
                    </div>
                    <div class="row">
                        <div class="col-sm-2">
                            <button type="button" class="btn btn-secondary btn-sm submit_btn">submit</button>
                        </div>
                    </div>
                </form>
            </div>
        </div>

        <div class="card">
            <div class="card-header">
                <h3 class="card-title ">Key Utility List View</h3>
            </div>

            <div class="card-body">
                <!-- CSV Button Section -->
                    <div class="row mb-3">
                    <div class="col-sm-12 col-md-6">
                        <button class="btn btn-secondary btn-sm" id="csvButton">CSV</button>
                    </div>

                    <div class="col-sm-12 col-md-5">
                        <form action="" method="get">
                            <div class="form-group">
                                <div class="input-group">
                                    <input type="text" class="form-control form-control-sm" name="search" placeholder="Search" aria-label="Search">
                                    <div class="input-group-append">
                                        <button class="btn btn-sm btn-secondary" type="submit">Search</button>
                                    </div>
                                </div>
                            </div>
                        </form>
                    </div>
                </div>

                <!-- Table Format -->
                <table class="table table-bordered table-striped">
                    <thead>
                        <tr>
                            <th>#</th>
                            <th>Key Name</th>
                            <th>Associated Columns</th>
                            <th>Actions</th>
                        </tr>
                    </thead>
                    <tbody>
                        @foreach($key_name as $index => $value)
                        <tr>
                            <td>{{ $index + 1 }}</td>
                            <td>{{ $value->key }}</td>
                            <td>
                                <div class="row">
                                    @foreach($key_utility_data as $d_val)
                                        @if($d_val->key_id == $value->id)
                                            <span class="badge badge-secondary black-text" style="margin-right: 10px; margin-bottom: 10px; display: inline-block;">
                                                {{ !empty($d_val->alias) ? $d_val->alias : $d_val->column_name }} ({{ $d_val->lob }})
                                                <img class="ml-2 del_img" src="{{ asset('Img/icons8-delete-trash-24.png') }}" alt="Delete Icon" del_id="{{ $d_val->id }}" style="cursor:pointer; width: 14px;">
                                            </span>
                                        @endif
                                    @endforeach
                                </div>
                            </td>
                            <td>
                                <i class="fa-regular fa-pen-to-square updt_icn" style="cursor:pointer;" val_id="{{ $value->id }}"></i>
                                <i class="fa-solid fa-trash ml-3 del_icn" style="cursor:pointer;" val_id="{{ $value->id }}"></i>
                            </td>
                        </tr>
                        @endforeach
                    </tbody>
                </table>
                <div class="mt-3 d-flex justify-content-between">
                    <div>
                        <ul class="pagination">
                            <li class="page-item"><a class="page-link" href="#">Previous</a></li>
                            <li class="page-item active"><a class="page-link" href="#">1</a></li>
                            <li class="page-item"><a class="page-link" href="#">2</a></li>
                            <li class="page-item"><a class="page-link" href="#">3</a></li>
                            <li class="page-item"><a class="page-link" href="#">Next</a></li>
                        </ul>
                    </div>
                </div>
            </div>

        </div>
        <div class="modal fade" id="del_mdl">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Default Modal</h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <p>This will delete all the columns related to this key are you sure to proceed </p>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" class="btn btn-primary del_cnf">Save changes</button>
                    </div>
                </div>

            </div>

        </div>
    </section>
    <script src="{{asset('Js/keyUtility.js')}}"></script>
@endsection
