@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <section class="content">

<div class="card card-secondary">
    <div class="card-header">

        <h3 class="card-title">Column visibility</h3>
    </div>
    <form method="post" >
        @csrf
        <div class="card-body">
            <div class="row">
                <div class="col-sm-6">
                    <div class="form-group">
                        <select name="lob_sel" id="" class="form-control" onchange="form.submit()" >
                            <option value="">Select Lob</option>
                            @foreach($lobs as $l)
                            <option value="{{$l->id}}" @if($selLob == $l->id) selected @endif>{{$l->lob}}</option>

                            @endforeach
                        </select>
                    </div>
                </div>
                <div class="col-sm-6">
                    <div class="form-group">
                        <input type="text" class="form-control" placeholder="search Columns here" name="search_col" id="">
                    </div>
                </div>
            </div>
            <div class="row">
            @php
            $not_show_column_array = ['_id', 'created_at', 'updated_at'];
            @endphp
                @if(empty($allColumns->toArray()))
                    <div class="col-sm-6">
                        <div class="form-group">
                            <div class="text-info">No Data is Available Please Check With Developers</div>
                        </div>
                    </div>
                @endif
                @if(empty($selLob))
                    @php
                    $allColumns = [];
                    @endphp
                    <div class="col-sm-6">
                        <div class="form-group">
                            <div class="text-info"> Please Select First Line Of Business For column Visibility</div>
                        </div>
                    </div>
                @endif



                @foreach ($allColumns as $key => $column)

                    @if(!in_array($column->column_name, $not_show_column_array))
                    <div class="col-sm-6">
                        <div class="form-group">
                            <div class="row">
                                <div class="custom-control custom-switch">
                                    @php
                                    $lobs_array = explode(',', $column->lob) ?? [];
                                    @endphp
                                    <input type="checkbox" class="custom-control-input" name="col_names[]" value="{{$column->id}}" id="{{$column->id}}" @if($column->is_visible == 'Y' && strpos($column->stage,$selStage)) checked @else ''  @endif>
                                    <label class="custom-control-label mr-3 colnms" for="{{$column->id}}">{{!empty($column->alias) ? $column->alias.' ('.$column->column_name.')' : $column->column_name}}</label>
                                </div>
                            </div>
                        </div>
                    </div>
                   @endif
                @endforeach
        </div>

    </form>
</div>
    </section>
    <script src="{{asset('Js/excel_upload_key_master.js')}}"></script>
@endsection
