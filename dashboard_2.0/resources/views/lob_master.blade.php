@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <section class="content">
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Column visibility</h3>
            </div>
                <div class="card-body">
                    <form method="post" name="lob_frm" >
                    @csrf
                    <div class="row">
                        @foreach ($lobs as $key => $column)
                                <div class="col-sm-6">
                                    <div class="form-group">
                                        <div class="custom-control custom-switch">
                                            <input type="checkbox" class="custom-control-input lobs_list"  id="{{$column->id}}" value="{{$column->id}}" @if($column->is_enabled == 'Y') checked @endif>
                                            <label class="custom-control-label mr-3" for="{{$column->id}}">{{$column->lob_name}}</label>
                                        </div>
                                    </div>
                                </div>
                        @endforeach
                    </div>
            </form>
            <a href="lob_data" class=" btn btn-sm btn-secondary">lob Edit</a>
        </div>
    </section>
    <script src="{{asset('Js/lob_master.js')}}"></script>
@endsection
