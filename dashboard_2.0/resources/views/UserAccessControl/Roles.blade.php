@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <!-- Main content -->

    <section class="content">
    <div class="card card-secondary">
    <div class="card-header">
        <h3 class="card-title">Roles Master</h3>
    </div>
        <form method="post" name="RoleMaster">
            @csrf
            <input type="hidden" name="apitoken" value="{{request()->cookie('Token')}}">
            <div class="card-body">
            <div class="row">
                <div class="col-sm-4">
                    <div class="form-group">
                        <label for="">Role Name</label>
                        <input type="text" maxlength="50" name="RoleName" class="form-control"  id="Role_id"
                               placeholder="Enter Role Name">
                    </div>
                </div>
                <div class="col-sm-4">
                    <div class="form-group">
                        <label for="">Usertype</label>
                        <select name="UsertypeID" id="UsertypeID" class="form-control">
                            <option value="">Select</option>
                            @foreach($userType as $Utype)
                                <option value="{{$Utype->id}}">{{$Utype->name}}</option>
                            @endforeach
                        </select>
                    </div>
                </div>
                <div class="col-sm-4">
                    <div class="form-group">
                        <label for="ReportingRoleID">Reporting Role</label>
                        <select name="ReportingRole" id="ReportingRoleID" class="form-control">
                            <option value="">Select</option>

                        </select>
                    </div>
                </div>
            </div>
                <button type="button" class="btn btn-secondary add_role">Submit</button>
            </div>
        </form>
    </div>
    <div class="card card-secondary">
    <div class="card-header">
        <h3 class="card-title">Assign Roles</h3>
    </div>
        <form method="post" name="RoleToUser">
            @csrf
            <div class="card-body">
            <div class="row">
                <div class="col-sm-4">
                    <div class="form-group">
                        <label for="IdRole">Role Name</label>
                       <select name="role_id" id="IdRole" class="form-control">
                        <option value="">Select Role To Assign User</option>
                       </select>
                    </div>
                </div>
                <div class="col-sm-4">
                    <div class="form-group">
                        <label for="">User</label>
                        <select name="user_id" id="UsertypeID" class="form-control">
                            <option value="">Select User</option>

                        </select>
                    </div>
                </div>

            </div>
                <button type="button" class="btn btn-secondary AssignRole">Submit</button>
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
                                <button class="btn btn-secondary buttons-copy buttons-html5" tabindex="0"
                                        aria-controls="example1" type="button"><span>CSV</span></button>
                            </div>
                        </div>
                        <div class="col-sm-12 col-md-6">
                            <div id="example1_filter" class="dataTables_filter"><label>Search:<input type="search" class="form-control form-control-sm" placeholder="" aria-controls="example1"></label>
                            </div>
                        </div>
                    </div>
                    <div class="row">
                        @foreach($ReportingRoles as $roles)
                        <div class="col-sm-3 mt-2">
                                <div class="card" >
                                    <div class="card-body">
                                        <h5 class="card-title">{{$roles->name}}</h5>
                                        <p class="card-text">User Type : {{!empty($roles->user_type) && isset($userTypeArr[$roles->user_type]) ? $userTypeArr[$roles->user_type] : ""}}
                                            <br>
                                            Reporting Role : {{!empty($roles->reporting_role) && isset($ReportingRolesArr[$roles->reporting_role]) ? $ReportingRolesArr[$roles->reporting_role] : ""}}
                                        </p>
                                        @if($roles->user_type >0 )
                                        @can('Role.edit')

                                        <a  class="btn btn-sm btn-secondary edt_btn mt-2 " uid="{{$roles->id}}" utype="{{$userTypeArr[$roles->user_type] ?? ''}}" rptrole="{{$ReportingRolesArr[$roles->reporting_role] ?? ''}}">Edit</a>
                                        <a  class="btn btn-sm btn-secondary del_btn mt-2 ml-2" uid="{{$roles->id}}">Delete</a>
                                        @endcan
                                        @else
                                            <br>
                                            <br>
                                            @endif
                                    </div>
                            </div>
                        </div>
                        @endforeach

                    </div>
                    <div class="row">
                        <div class="col-sm-12 col-md-5">
                            <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1
                                to 10 of {{$totalRecords}} entries
                            </div>
                        </div>
                        <div class="col-sm-12 col-md-7">
                            <div class="dataTables_paginate paging_simple_numbers" id="example1_paginate">
                                <ul class="pagination">
                                    <li class="paginate_button page-item previous {{$page == 1 || empty($page)  ? 'disabled' :  ''}}" id="example1_previous"><a
                                            href="?page={{$page < 0 ? '' : ($page > ceil($totalRecords) ? '' : $page - 1)}}" aria-controls="example1" data-dt-idx="0" tabindex="0"
                                            class="page-link">Previous</a></li>
                                    @for($i=1;$i<=ceil($totalRecords/10);$i++)
                                    <li class="paginate_button page-item "><a href="?page={{$i}}" aria-controls="example1" data-dt-idx="1" tabindex="0" class="page-link">{{$i}}</a></li>
                                    @endfor
                                    <li class="paginate_button page-item next" id="example1_next"><a href="?page={{$i = $i<ceil($totalRecords/10) ? $i+1 : $i}}" aria-controls="example1" data-dt-idx="7" tabindex="0" class="page-link">Next</a>
                                    </li>
                                </ul>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
{{--            roles edit modal --}}
            <div class="modal fade" id="edit_modal" style="display: none;" aria-hidden="true">
                <div class="modal-dialog">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h4 class="modal-title">Edit Roles</h4>
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
                                            <label for="sub_stage">Role Name</label>
                                            <input type="text" class="form-control" id="roleName"  placeholder="Enter Update Role Name" >
                                            <label for="sub_stage">user type</label>
                                            <select class="form-control" name="usertype">
                                                <option value="">select Usertype</option>
                                            </select>
                                            <label for="sub_stage">Reporting role</label>
                                               <select class="form-control" name="reportingrole">
                                                   <option value=""> select Reporting role</option>
                                               </select>
                                            <input type="hidden" name="RoleId" value="">

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

        </div>
    </section>

    <script src="{{asset('Js/Roles.js')}}"></script>


@endsection
