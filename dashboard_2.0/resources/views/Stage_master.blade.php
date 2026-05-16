@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <!-- Main content -->

    <link rel="stylesheet" href="{{ asset('plugins/datatables-bs4/css/dataTables.bootstrap4.min.css') }}">
    <link rel="stylesheet" href="{{ asset('plugins/datatables-responsive/css/responsive.bootstrap4.min.css') }}">
    <link rel="stylesheet" href="{{ asset('plugins/datatables-buttons/css/buttons.bootstrap4.min.css') }}">
    <script src="{{ asset('plugins/jquery/jquery.min.js') }}"></script>
    <section class="content">
        <input type="hidden" name="apitoken" value="{{request()->cookie('Token')}}">
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Stage Master</h3>
            </div>
            <form method="post" name="stage_master">
                @csrf
                <div class="card-body">
                    <div class="form-group">
                        <label for="">Enter Stage Name</label>
                        <input type="text" maxlength="50" name="stage_name" class="form-control"  id="exampleInputEmail1"
                            placeholder="Enter Stage Name">
                    </div>

                    <button type="button" class="btn btn-secondary c_stage">Submit</button>
                </div>

            </form>
        </div>



        <!-- sub stage master code form here -->
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Sub Stage Master</h3>
            </div>
            <form method="post" name="sub_stage_master" onsubmit="javascript:void(0);">
                @csrf
                <div class="card-body">
                    <div class="row">
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="exampleInputEmail1">Select Stage master</label>
                                <select name="stage_mstr"  class="custom-select">
                                    <option value="">Please Select Stage Master</option>
                                    @foreach ($selectStage as $item)
                                        <option value="{{ $item->id }}">{{ $item->stage_name }}</option>
                                    @endforeach
                                </select>
                            </div>
                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="exampleInputPassword1">Sub stage master</label>
                                <select name="sub_stage_name"  class="custom-select">
                                    <option value="">Please Select Stage Master</option>

                                    @foreach($sub_stage_master as $sub_stg_key => $sub_stg)
                                        <option value="{{ $sub_stg_key }}">{{ $sub_stg }}</option>

                                    @endforeach
                                </select>
                            </div>
                        </div>
                    </div>
                    <button type="button" class="btn btn-secondary sbt">Submit</button>
                    <button type="button" class="btn btn-secondary show_add">Add New Sub Stage</button>
                    <button type="button" class="btn btn-secondary renewalstg">Renewal SubStages</button>
                    <div class="if_add">

                    <div class="row mt-3">
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Enter new Sub Stage Name</label>
                                <input type="text" maxlength="50" name="new_sub_stage_name" class="form-control"  id="exampleInputEmail1"
                                       placeholder="Enter Stage Name">
                            </div>
                        </div>

                    </div>
                        <button type="button" class="btn btn-secondary sub_new_stage">Submit</button>
                    </div>
                </div>

            </form>
        </div>

        <div class="card">
            <div class="card-header">
                <h3 class="card-title">DataTable with default features</h3>
            </div>

            <div class="card-body">
                <div id="example1_wrapper" class="dataTables_wrapper dt-bootstrap4">
                    <div class="row">
                        <div class="col-sm-12 col-md-6">
                            <div class="dt-buttons btn-group flex-wrap">
                                <button
                                    class="btn btn-secondary buttons-excel buttons-html5" tabindex="0"
                                    aria-controls="example1" type="button"><span>Excel</span></button>
                                <button
                                    class="btn btn-secondary buttons-pdf buttons-html5" tabindex="0"
                                    aria-controls="example1" type="button"><span>PDF</span></button>
                            </div>
                        </div>
                        <div class="col-sm-12 col-md-6">
                            <div id="example1_filter" class="dataTables_filter">
                                <form  method="get" name="stage_search" action="stagemaster">
                                <input type="search" class="form-control form-control-sm" name="search_val" value="{{$search_val}}"  aria-controls="example1" placeholder="Search">
                                <button type="submit" class="btn btn-secondary btn-sm">Search</button>
                                </form>
                            </div>
                        </div>
                    </div>
                    <div class="text-danger">To Modify The Sub Stages Please Click On specific Sub stages</div>
                    <div class="row">
                        <div class="col-sm-12">
                            <table id="example1" class="table table-bordered table-striped dataTable dtr-inline"
                                aria-describedby="example1_info">
                                <thead>
                                    <tr>
                                        <th class="sorting sorting_asc" tabindex="0" aria-controls="example1"
                                            rowspan="1" colspan="1" >
                                            Sr.no</th>
                                        <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1"
                                            colspan="1" >Stage
                                        </th>
                                        <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1"
                                            colspan="1" >
                                            Sub Stage </th>
                                        <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1"
                                            colspan="1" >
                                            Priority</th>
                                        <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1"
                                            colspan="1" >
                                            Action </th>
                                    </tr>
                                </thead>
                                <tbody>

                                        @php
                                        $i=1;
                                        $count_stage = count($stageMaster) ?? 0;
                                        @endphp
                                        @foreach($stageMaster as $item)
                                            @php
                                            $list_sub_stages = explode(',',$item->sub_stage_name);
                                            @endphp
                                            <tr class="odd">
                                                <td class="dtr-control sorting_1" tabindex="0">{{$i}}</td>
                                                <td>
                                                    <div class="row edit_stage " stg_id="{{$item->id}}">
                                                    {{$item->stage_name}}<i class=" fas fa-pen-square ml-2"></i>
                                                    </div>
                                                </td>
                                                <td>
                                                    @foreach($list_sub_stages as $btn_substages)
                                                    @if(!empty($btn_substages))
                                                    <button class="btn btn-secondary btn-sm sb_st_btn mt-2 " p_st_id="{{$item->id}}" p_sub_st_id="{{$btn_substages}}">{{$sub_stage_master[$btn_substages]}} <i class=" fas fa-pen-square"></i></button>

                                                    @endif
                                                    @endforeach
                                                </td>
                                                <td>
                                                    <div class="form-group">
                                                        <select name="stage_priority" id="" class="custom-select" old_val="{{$item->priority}}" stg_id="{{$item->id}}">
                                                            <option value="">Set Priority </option>
                                                            @for($j=1;$j<=$count_stage;$j++)
                                                            <option value="{{$j}}" {{$item->priority == $j ? 'selected' : ''}}  >{{$j}}</option>
                                                            @endfor
                                                        </select>
                                                    </div>
                                                </td>
                                                <td>
                                                    <button class="btn btn-danger  mt-2 deletebtn" stage_del_id="{{$item->id}}">Delete</button>
                                                </td>
                                            </tr>
                                            @php
                                            $i++;
                                            @endphp
                                        @endforeach

                                </tbody>

                            </table>
                        </div>
                    </div>
                    @php
                    $count = $count_stage;
                    $page_nos = ceil($count/10);
                   $current_page = $stageMaster->currentPage();
                    @endphp
                    <div class="row"><div class="col-sm-12 col-md-5"><div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1 to 10 of {{$count}} entries</div></div>
                        <div class="col-sm-12 col-md-7"><div class="dataTables_paginate paging_simple_numbers" id="example1_paginate">
                                <ul class="pagination">

                                    <li class="paginate_button page-item previous {{$current_page == 1 ? 'disabled' : ''}}" id="example1_previous"><a href="/StageMaster?page={{$page_nos - 1}}" aria-controls="example1" data-dt-idx="0" tabindex="0" class="page-link" >Home</a></li>
                                    <li class="paginate_button page-item previous {{$current_page == 1 ? 'disabled' : ''}}" id="example1_previous"><a href="/StageMaster?page={{$page_nos - 1}}" aria-controls="example1" data-dt-idx="0" tabindex="0" class="page-link" >Previous</a></li>
                                        @if($current_page > 3 )
                                            <li class="paginate_button page-item disabled"><a href="/StageMaster?page={{$current_page}}" aria-controls="example1" data-dt-idx="1" tabindex="0" class="page-link">....</a></li>
                                        @endif
                                    @for($i=1;$i<=$page_nos;$i++)
                                    <li class="paginate_button page-item {{$current_page == $i ? 'active' : ''}}"><a href="/StageMaster?page={{$i}}" aria-controls="example1" data-dt-idx="1" tabindex="0" class="page-link">{{$i}}</a></li>

                                    @endfor

                                    <li class="paginate_button page-item {{$current_page == $page_nos ? 'disabled' : ''}}"><a href="/StageMaster?page={{$current_page + 1}}" aria-controls="example1" data-dt-idx="7" tabindex="0" class="page-link" >Next</a></li>
                                    <li class="paginate_button page-item {{$current_page == $page_nos ? 'disabled' : ''}}"><a href="/StageMaster?page={{$current_page + 1}}" aria-controls="example1" data-dt-idx="7" tabindex="0" class="page-link" >End</a></li>
                                </ul>
                            </div>
                        </div></div>
                </div>
            </div>

        </div>
        <br>
        <br>
        <br>
        {{--  modal for sub stages      --}}
        <div class="modal fade" id="modal-default" style="display: none;" aria-hidden="true">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Edit Sub Stage </h4>
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
                                    <input type="text" class="form-control" id="sub_stage" name="mdl_sb_stg" placeholder="Enter Sub Stage" disabled>
                                        <input type="hidden" name="mdl_stg_id" value="">
                                        <input type="hidden" name="mdl_sub_stg_id" value="">
                                        <input type="hidden" name="mdl_sb_stg_old" value="">

                                <button type="button" class="btn btn-secondary mt-4 del_sub_stage">Delete</button>
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
        {{--  modal for parent stages     --}}
        <div class="modal fade" id="del_stage_mdl">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Delete Stage</h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <p class="text-danger"> If You Delete The Main Stage Then It Will Delete All The SubStages Along With It Please Proceed With Precaution</p>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <form method="post" name="stage_del_frm">
                            @csrf

                        <input type="hidden" name="del_stg_id" value="">
                        </form>
                        <button type="button" class="btn btn-secondary del_stage">Delete</button>
                    </div>
                </div>

            </div>

        </div>

        <div class="modal fade" id="edt_stage_mdl">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Update Stage</h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <div class="row">
                            <div class="col-sm-12">
                                <div class="form-group">
                                    <form name="ed_stage_frm" method="post">

                                    <label for="edt_stage">Stage</label>
                                        @csrf
                                    <input type="text" class="form-control" id="edt_stage" name="edt_stage" placeholder="Enter Stage">
                                    <input type="hidden" name="edt_stage_id" >
                                    </form>
                                </div>
                            </div>
                        </div>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <form method="post" name="stage_del_frm">
                            @csrf

                            <input type="hidden" name="del_stg_id" value="">
                        </form>
                        <button type="button" class="btn btn-secondary edt_stage">Update</button>
                    </div>
                </div>

            </div>

        </div>
        {{-- modal for sub stages renewal add --}}
        <div class="modal fade" id="renewal_substage">
            <div class="modal-dialog modal-xl">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Update Stage</h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <div class="row">
                            <label for="exampleInputPassword1">Sub stage master</label>
                            <div class="col-sm-12">
                                <div class="form-group">
                                    <form method="post" name="renewal_stages">

                                        <select name="sub_stage_name_renewal[]" multiple class="select2 select2-hidden-accessible form-control" data-placeholder="please select Multiple stages for renewal" style="width: 100%;">

                                            @foreach($sub_stage_master as $sub_stg_key => $sub_stg)
                                            <option value="{{ $sub_stg_key }}">{{ $sub_stg }}</option>

                                            @endforeach
                                        </select>
                                    </form>
                                </div>
                            </div>
                        </div>
                        <div class="row">
                            @foreach ($renewal_stages as $keyrs => $rs)
                            <div class="col-sm-3">
                                <button type="button" class="btn btn-secondary btn-sm sel_rene_stg" id="{{ $keyrs }}">{{ $rs }} <i class="fa-solid fa-delete-left"></i></button>
                            </div>
                                @endforeach
                        </div>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" class="btn btn-secondary add_renewal_stg">Update</button>
                    </div>
                </div>

            </div>

        </div>

    </section>
    <!-- /.content -->
    <script src="{{asset('Js/Stage_master.js')}}"></script>

@endsection
