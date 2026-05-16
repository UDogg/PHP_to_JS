@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <section class="content">
<div class="row">

    <div class="col-md-12">

        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Quick Example</h3>
            </div>
            <form method="post" name="filter_master" >
                @csrf
                <div class="card-body">
                    <div class="row">
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="FilterNameID">Filter Name</label>
                                <input type="text" maxlength="75" class="form-control" id="FilterNameID" name="filter_name" placeholder="Enter Filter Name">
                            </div>
                        </div>
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="FilterTypeID">Filter Type</label>
                              <select class="form-control" name="filter_type" id="FilterTypeID">
                                  <option value=''>select Type</option>
                                  <option value="1">Stages</option>
                                  <option value="2">Key</option>
                                  <option value="3">Date</option>
                                  <option value="4">Others</option>
                              </select>
                            </div>
                        </div>
                        <div class="col-sm-4 stage_div">
                            <div class="form-group">
                                <label for="StagesID">Stages</label>
                              <select class="form-control" name="stage" id="StagesID">
                                  <option value="">select Type</option>
                                @foreach($stages as $stg)
                                    <option value="{{$stg->id}}">{{$stg->stage_name}}</option>
                                @endforeach

                              </select>
                            </div>
                        </div>
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="FilterTypeID">Line Of Bussiness(LOB)</label>
                              <select class="select2 select2-hidden-accessible form-control" multiple name="lob[]" style="width: 100%;" id="LobID" data-placeholder="Select LOB">
                                  <option value="">select Type</option>
                                @foreach($lobs as $l)
                                    <option value="{{$l->id}}">{{$l->lob_name}}</option>
                                @endforeach

                              </select>
                            </div>
                        </div>
                        <div class="col-sm-4 col_div">
                            <div class="form-group">
                                <label for="exampleInputFile">Columns</label>
                                <div class="input-group">
                                    <div class="custom-file">
                                        <select name="columns" id=""  data-placeholder="please select values" class="select2 select2-hidden-accessible form-control" style="width: 100%;"  tabindex="-1" aria-hidden="true">
                                            <option value="">Select Column</option>

                                        </select>
                                    </div>
                                </div>
                            </div>
                        </div>
                        </div>
                    <div class="row">

                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="FilterStatusID">key</label>
                                <input type="text" name="key" class="form-control" placeholder="Enter Key for option value"  id="">
                            </div>
                        </div>
                        <div class="col-sm-4">

                            <div class="form-group">
                                <label for="FilterStatusID">value</label>
                                <input type="text" name="value" class="form-control" placeholder="Enter Display Name For Option" id="">
                            </div>
                        </div>
                        <div class="col-sm-2">
                        </div>
                    </div>
                            <button type="button" class="btn btn-secondary btn-sm add_pair">Add</button>
                </div>
            </form>
        </div>
    </div>
</div>

        <div class="row">
            <div class="col-12">

                <div class="card">
                    <div class="card-header">
                        <h3 class="card-title">Filter Master List View</h3>
                    </div>

                    <div class="card-body">
                        <div id="example1_wrapper" class="dataTables_wrapper dt-bootstrap4">
                            <div class="row">
                                <div class="col-sm-12 col-md-6">
                                    <div class="dt-buttons btn-group flex-wrap">
                                        <button class="btn btn-secondary buttons-copy buttons-html5" tabindex="0"
                                                aria-controls="example1" type="button"><span>CSV</span></button>

                                    </div>
                                </div>
                                <div class="col-sm-12 col-md-6">
                                    <div id="example1_filter" class="dataTables_filter"><label>Search:<input
                                                type="search" class="form-control form-control-sm" placeholder=""
                                                aria-controls="example1"></label></div>
                                </div>
                            </div>
                            <div class="row">
                                <div class="col-sm-12">
                                    <table id="example1" class="table table-bordered table-hover dataTable dtr-inline" aria-describedby="example1_info">
                                        <thead>
                                            <tr>
                                                <th>SR.no</th>
                                                <th>Name</th>
                                                <th>key,value</th>
                                                <th>Action</th>
                                            </tr>
                                        </thead>
                                        <tbody>
                                            @foreach($allData as $data)
                                            <tr class="odd">
                                                <td class="dtr-control sorting_1" tabindex="0">{{$loop->iteration}}</td>
                                                <td>{{$data['filtername']}}</td>
                                                <td>{{$data['key']}},{{$data['value']}}</td>
                                                <td>
                                                    <button class="btn btn-sm btn-primary editbtn"  data-name="{{$data['filtername']}}" data-key="{{$data['key']}}" data-value="{{$data['value']}}" data-id="{{$data['id']}}" >Edit</button>
                                                    <button class="btn btn-sm btn-danger deletebtn" data-id="{{$data['id']}}">Delete</button>
                                                </td>
                                            </tr>
                                            @endforeach
                                        </tbody>
                                    </table>
                                    
                                </div>
                            </div>
                            <div class="row">
                                <div class="col-sm-12 col-md-5">
                                    <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1
                                        to @if ($count < 10) {{$count}} @else 10 @endif  of {{$count}} entries
                                    </div>
                                </div>
                                <div class="col-sm-12 col-md-7">
                                    <div class="dataTables_paginate paging_simple_numbers" id="example1_paginate">
                                        <ul class="pagination">
                                            @php
                                            $perpage = '';
                                            $i=0;
                                            $pageCount = ceil($count/10);
                                            @endphp
                                            <li class="paginate_button page-item previous disabled" id="example1_previous"><a
                                                    href="#" aria-controls="example1" data-dt-idx="0" tabindex="0"
                                                    class="page-link">Previous</a></li>
                                            @for($i=1;$i<=$pageCount;$i++)
                                            <li class="paginate_button page-item "><a href="?page={{$i}}" aria-controls="example1" data-dt-idx="1" tabindex="0" class="page-link">{{$i}}</a></li>
                                            @endfor
        
                                            <li class="paginate_button page-item next" id="example1_next"><a href="?page={{$i = $i >= $pageCount ? $i+1 : $i}}" aria-controls="example1" data-dt-idx="7" tabindex="0" class="page-link">Next</a>
                                            </li>
                                        </ul>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>

                </div>

            </div>

        </div>




        <div class="modal fade" id="modal-default" style="display: none;" aria-hidden="true">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Edit Filter Name </h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">

                        <div class="row">
                            <div class="col-sm-10">
                                <div class="form-group">
                                    <form method="post" name="mdl_stage_frm" >
                                            @csrf
                                    <label for="sub_stage">Sub Stage</label>
                                    <input type="text" class="form-control" id="sub_stage" name="mdl_sb_stg" placeholder="Enter Sub Stage">
                                        <input type="hidden" name="mdl_stg_id" value="">
                                        <input type="hidden" name="mdl_sub_stg_id" value="">
                                        <input type="hidden" name="mdl_sb_stg_old" value="">

                                {{-- <button type="button" class="btn btn-secondary mt-4 del_sub_stage">Delete</button> --}}
                                    </form>
                                </div>
                            </div>
                            <div class="col-sm-2">
                            </div>
                        </div>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" class="btn btn-primary cls_mdl">Save changes</button>
                    </div>
                </div>

            </div>

        </div>





    </section>




<!-- Modal for Edit -->
<div class="modal fade" id="editModal" tabindex="-1" aria-labelledby="editModalLabel" aria-hidden="true">
    <div class="modal-dialog">
        <div class="modal-content">
            <div class="modal-header">
                <h5 class="modal-title" id="editModalLabel">Edit Filter Master Data</h5>
                <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                    <span aria-hidden="true">&times;</span>
                </button>
            </div>
            <div class="modal-body">
                <form id="editForm">
                    <input type="hidden" id="editId">
                    <div class="form-group">
                        <label for="editName">Filter Name</label>
                        <input type="text" class="form-control" id="editName" required>
                    </div>
                    <div class="form-group">
                        <label for="editKey">Filter Key</label>
                        <input type="text" class="form-control" id="editKey" required>
                    </div>
                    <div class="form-group">
                        <label for="editValue"> Filter Value</label>
                        <input type="text" class="form-control" id="editValue" required>
                    </div>
                    <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                    <button type="submit" class="btn btn-primary">Update</button>
                </form>
            </div>
        </div>
    </div>
</div>
<script src="{{asset('Js/PolStatusMaster.js')}}"></script>
@endsection
