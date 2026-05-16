@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <!-- Main content -->
    <section class="content">

        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Access Controll & Permission Master</h3>
            </div>

            <form method="post" name="AssignRole">
                @csrf
                <input type="hidden" name="apitoken" value="{{request()->cookie('Token')}}">
                <div class="card-body">
                    <div class="row">

                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="">Usertype Filter</label>
                                <select name="usertype_filter" id="usertypeFilter" class="form-control">
                                    <option value="">Select</option>

                                </select>
                            </div>
                        </div>
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="">Role</label>
                                <select name="role_id" id="UsertypeID" class="form-control">
                                    <option value="">Select</option>
                                 

                                </select>
                            </div>
                        </div>
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="">Permission </label>
                                <select name="permission_id[]" id="permissionsDropdown" class="select2 select2-hidden-accessible form-control" data-placeholder="please select values" style="width: 100%;" multiple>
                                    <option value="">Select</option>
                                    @foreach($permissions  as $permission)
                                        <option value="{{$permission->id}}"> {{$permission->name}}</option>
                                    @endforeach
                                </select>
                            </div>
                        </div>

                    </div>
                    <button type="button" class="btn btn-secondary GiveAccess">Submit</button>
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

                                <button class="btn btn-secondary buttons-csv buttons-html5" tabindex="0"
                                        aria-controls="example1" type="button"><span>CSV</span></button>

                            </div>
                        </div>
                        <div class="col-sm-12 col-md-6">
                            <div id="example1_filter" class="dataTables_filter"><label>Search:<input type="search" class="form-control form-control-sm" placeholder="" aria-controls="example1"></label>
                            </div>
                        </div>
                    </div>
                    <div class="row">
                        <div class="col-sm-12">
                            <table id="example1" class="table table-bordered table-striped dataTable dtr-inline"
                                   aria-describedby="example1_info">
                                <thead>
                                <tr>
                                    <th class="sorting sorting_asc" tabindex="0" aria-controls="example1" rowspan="1"
                                        colspan="1" aria-sort="ascending"
                                        aria-label="Rendering engine: activate to sort column descending">Sr.no</th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                        aria-label="Browser: activate to sort column ascending">Permission
                                    </th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                        aria-label="Platform(s): activate to sort column ascending">Roles
                                    </th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                        aria-label="Platform(s): activate to sort column ascending">Action
                                    </th>

                                </tr>
                                </thead>
                                <tbody>
                                   @foreach($dataPermission as $key_d => $data)
                                    <tr class="even">
                                       <td>{{$loop->iteration}}</td>
                                       <td>{{$key_d}}</td>
                                            <td>
                                            @foreach($data as $d)
                                            @php
                                            $permission_id = $d->permission_id;
                                            $roles_id = $d->role_id;
                                            @endphp

                                                    <button class="btn btn-secondary btn-sm revoke_permission" p_id = {{ $permission_id}} r_id={{$roles_id}}>{{$d->role_name}}<i class="fa fa-trash"></i></button>
                                            @endforeach
                                            </td>
                                        <td>
                                            {{-- <button class="btn btn-secondary edit" data-id="{{$permission_id}}" str="{{$key_d}}">Edit</button> --}}
                                            <button class="btn btn-secondary delete" data-id="{{$permission_id}}">Delete</button></td>
                                    </tr>
                                   @endforeach

                                </tbody>

                            </table>
                        </div>
                    </div>
                    <div class="row">
                        <div class="col-sm-12 col-md-5">
                            <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1
                                to 10 of 57 entries
                            </div>
                        </div>
                        <div class="col-sm-12 col-md-7">
                            <div class="dataTables_paginate paging_simple_numbers" id="example1_paginate">
                                <ul class="pagination">
                                    <li class="paginate_button page-item previous disabled" id="example1_previous"><a
                                            href="#" aria-controls="example1" data-dt-idx="0" tabindex="0"
                                            class="page-link">Previous</a></li>
                                    <li class="paginate_button page-item active"><a href="#" aria-controls="example1" data-dt-idx="1" tabindex="0" class="page-link">1</a></li>
                                    <li class="paginate_button page-item "><a href="#" aria-controls="example1" data-dt-idx="2" tabindex="0" class="page-link">2</a></li>
                                    <li class="paginate_button page-item "><a href="#" aria-controls="example1" data-dt-idx="3" tabindex="0" class="page-link">3</a></li>
                                    <li class="paginate_button page-item next" id="example1_next"><a href="#" aria-controls="example1" data-dt-idx="7" tabindex="0" class="page-link">Next</a>
                                    </li>
                                </ul>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

        </div>
        <div class="modal fade" id="modal-default">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Default Modal</h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <p>Are You Sure You Want To Unlink This Role and Permission </p>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" class="btn btn-secondary cnf_delete">Delete</button>
                    </div>
                </div>

            </div>

        </div>
            <!-- Modal -->
        <div class="modal fade" id="editModal" tabindex="-1" aria-labelledby="editModalLabel" aria-hidden="true">
            <div class="modal-dialog">
            <div class="modal-content">
                <div class="modal-header">
                <h5 class="modal-title" id="editModalLabel">Edit Permission</h5>
                <button type="button" class="btn-close" data-dismiss="modal" aria-label="Close"></button>
                </div>
                <div class="modal-body">
                <form id="editForm">
                    <input type="hidden" id="permissionId" name="permission_id">
                    <input type="hidden" id="roleId" name="role_id">
                    <input type="text" id="roleName" name="role_name" class="form-control">
                </form>
                </div>
                <div class="modal-footer">
                <button type="button" class="btn btn-secondary" class="btn-close" data-dismiss="modal" aria-label="Close">Close</button>
                <button type="button" class="btn btn-primary" id="revokeUserPermission">Delete</button>
                </div>
            </div>
            </div>
        </div>
        

    </section>
    <script src="{{asset('Js/AccessControl.js')}}"></script>
@endsection
