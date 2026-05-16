@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    @php
    $user = \Illuminate\Support\Facades\Auth::user();
    @endphp
    <!-- Main content -->
    <section class="content">
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">User Types Master</h3>
            </div>
            <form method="post" name="UserTypeMaster" action="{{ route('UserTypes.createUserType') }}">
                @csrf
                <input type="hidden" name="apitoken" value="{{request()->cookie('Token')}}">
                <div class="card-body">
                    <div class="row">

                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="">User Type</label>
                                <input type="text" maxlength="50" name="UserType" class="form-control"  id="Type_id"
                                       placeholder="Enter User Type">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>
                        <div class="col-sm-4">
                            <div class="form-group">
                                <label for="">User Identifier</label>
                                <input type="text" maxlength="50" name="Userident" class="form-control"  id="identy_id"  placeholder="Enter User Type Unique Identifier">
                              
                            </div>
                        </div>
                        <div class="col-sm-2">
                            <div class="form-group">
                                <div class="custom-control custom-switch">
                                    <input type="checkbox" class="custom-control-input is_active" id="activeId" name="is_active_box" value="Y">
                                    <input type="hidden" name="is_active" value="" id="checkIsactive">
                                    <label class="custom-control-label mr-3 mt-5" for="activeId">Is Active</label>
                                </div>
                            </div>
                        </div>
                    </div>
                    <button type="button" class="btn btn-secondary addBtn">Submit</button>
                </div>
            </form>
        </div>
        <div class="card">
            <div class="card-header">
                <h3 class="card-title">Once the UserType Identifier is Created Then It Cannot Be Modified</h3>
            </div>

            <div class="card-body">
                <div id="example1_wrapper" class="dataTables_wrapper dt-bootstrap4">
                    <div class="row">
                        <div class="col-sm-12 col-md-6">
                            <div class="dt-buttons btn-group flex-wrap">
                                <button class="btn btn-secondary buttons-copy buttons-html5" tabindex="0"
                                        aria-controls="example1" type="button"><span>CSV</span></button>
                                <button class="btn btn-secondary buttons-copy buttons-html5 ml-2 dropdown-toggle" tabindex="0"
                                        aria-controls="example1" type="button" id="dropdownMenuButton" data-toggle="dropdown" ><span>Record Count</span></button>
                                <div class="dropdown-menu" aria-labelledby="dropdownMenuButton">
                                    <a class="dropdown-item" href="#">10</a>
                                    <a class="dropdown-item" href="#">50</a>
                                    <a class="dropdown-item" href="#">100</a>
                                </div>
                            </div>
                        </div>
                        <div class="col-sm-12 col-md-6">
                            <form method="get" name="search_frm"  action="{{route('UserTypes.index')}}">

                            <div id="example1_filter" class="dataTables_filter">
                                <input type="search" class="form-control form-control-sm" name="search_val" placeholder="Enter Search Value" aria-controls="example1">
                                <button class="btn btn-secondary btn-sm ml-2 search_btn">Search</button>
                            </div>
                            </form>
                        </div>
                    </div>
                    <div class="row">

                        @foreach($AllUsertype as $Utype)

                        <div class="col-sm-3 mt-3">
                            <div class="card" >
                                <div class="card-body">
                                    <h5 class="card-title">{{$Utype->name}}</h5>
                                    <p class="card-text">User Identifier : {{$Utype->Identifier}}
                                        <br>
                                    created At : {{\Carbon\Carbon::parse($Utype->created_at)->format('d-m-Y')}}
                                    </p>
                                    @if($user->can('usertype.edit'))
                                    <a  class="btn btn-sm btn-secondary edt_btn mt-2 " data-is-active="{{ $Utype->is_active }}" uid="{{$Utype->id}}">Edit</a>
                                    @endif
                                    @if($user->can('usertype.delete'))

                                    <a  class="btn btn-sm btn-secondary del_btn mt-2 ml-2" uid="{{$Utype->id}}">Delete</a>
                                    @endif
                                </div>
                            </div>
                        </div>
                        @endforeach

                    </div>
                    <div class="row">
                        <div class="col-sm-12 col-md-5">
                            <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1
                                to 10 of {{$count}} entries
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
                            <div class="row">
                                <div class="col-12">
                                    <div class="card">
                                        <div class="card-body">
                                            <table id="usertype-table-body" class="table">
                                                <thead>
                                                    <tr>
                                
                                                        <th>Usertype</th>
                                                        <th>Identifier</th>
                                                        <th>Is_active</th>
                                                        <th>Username</th>
                                                        <th>Actions</th>
                                                    </tr>
                                                </thead>
                                                <tbody>
                                                    @if(isset($users) && count($users) > 0)
                                                        @foreach ($users as $user)
                                                            <tr>
                                                                <td>{{ $user->name  }}</td>
                                                                <td>{{ $user->Identifier  }}</td>
                                                                <td>{{ $user->is_active }}</td>
                                                                <td>{{ $user->username }}</td>
                                                                <td>
                                                                    <button class="btn btn-sm btn-primary edit-section-field"
                                                                        data-id="{{ $user->id }}"
                                                                        data-name="{{ $user->name }}"
                                                                        data-toggle="modal"
                                                                        data-target="#editUserFieldModal">
                                                                        Edit
                                                                    </button>
                                                                </td>
                                                            </tr>
                                                        @endforeach
                                                    @else
                                                        <tr>
                                                            <td colspan="9" class="text-center">No Usertype's data available.</td>
                                                        </tr>
                                                    @endif
                                
                                
                                
                                                </tbody>
                                
                                            </table>
                                        </div>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <div class="modal fade" id="editUserFieldModal" tabindex="-1" role="dialog" aria-labelledby="editUserModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editUserModalLabel">Edit Username</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editUsertypeForm">
                                @csrf
                                <input type="hidden" name="_method" value="PUT">
                                <input type="hidden" name="apitoken" value="{{ request()->cookie('Token') }}">
                                <input type="hidden" id="usertype_id" name="usertype_id">
            
                                <div class="form-group">
                                    <label for="editusername">Username</label>
                                    <input type="text" class="form-control" id="editusername" name="editusername">
                                </div>
                                <div class="form-group">
                                    <label for="reset_password">Reset Password</label>
                                    <select class="form-control" id="reset_password" name="reset_password">
                                        <option value="">Select</option>
                                        <option value="Y">Yes</option>
                                        <option value="N">No</option>
                                    </select>
                                </div>
                                
            
                                <div class="modal-footer">
                                    <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                                    <button type="submit" class="btn btn-dark">Save Changes</button>
                                </div>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

        </div>
    </section>

    <script src="{{asset('Js/Usertype.js')}}"></script>


@endsection
