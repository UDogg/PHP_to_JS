@extends('layout.app', ['title' => 'Menu Master'])
<!-- Main content -->
@section('content')
<section class="content">
    <div class="row">
        <div class="col-12 col-sm-12">
            <div class="card card-secondary card-outline card-tabs">
                <div class="card-header p-0 pt-1 border-bottom-0">
                    <ul class="nav nav-tabs" id="custom-tabs-three-tab" role="tablist">
                        <li class="nav-item">
                            <a class="nav-link active" id="custom-tabs-three-home-tab" data-toggle="pill"
                                href="#MainMenu" role="tab" aria-controls="custom-tabs-three-home"
                                aria-selected="true">Main Menu Master</a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" id="custom-tabs-three-profile-tab" data-toggle="pill" href="#SubMenu"
                                role="tab" aria-controls="custom-tabs-three-profile" aria-selected="false">Sub Menu
                                Master</a>
                        </li>

                    </ul>
                </div>
                <div class="card-body">
                    <div class="tab-content" id="custom-tabs-three-tabContent">
                        <div class="tab-pane fade active show" id="MainMenu" role="tabpanel"
                            aria-labelledby="custom-tabs-three-home-tab">
                            <form name="menuMaster" method="post">
                                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                                @csrf
                                <div class="form-group">
                                    <label for="MenuName">Menu Name</label>
                                    <input type="text" class="form-control" name="menu" id="MenuName"
                                        placeholder="Enter Main Menu Name">
                                </div>
                                <div class="form-group">
                                    <label for="routeName">Route Name</label>
                                    <input type="text" class="form-control" name="route" id="routeName"
                                        placeholder="Menu Route">
                                </div>
                                <div class="row">
                                    <div class="col-sm-6">
                                        <div class="form-group">
                                            <label for="routeName">IS FrontEnd</label>
                                            <input type="text" class="form-control" name="FrontendUrlMainMenu"
                                                id="frontendId" placeholder="Enter FrontEnd Url">
                                        </div>

                                    </div>
                                    <div class="col-sm-6">
                                        <div class="form-group">
                                            <label for="routeName">FrontEnd Url</label>
                                            <select class="form-control" name="IsFrontEndMainMenu">
                                                <option value="N">N</option>
                                                <option value="Y">Y</option>
                                            </select>
                                        </div>

                                    </div>
                                </div>
                                <div class="row">
                                    <div class="col-sm-6">
                                        <div class="form-group">
                                            <label for="exampleInputFile">Menu Icon</label>
                                            <div class="form-group">
                                                <input type="text" class="form-control"
                                                    placeholder="Enter The Menu Icon" name="icon" id="exampleInputFile">

                                            </div>
                                        </div>

                                    </div>
                                    <div class="col-sm-6">
                                        <div class="form-group">
                                            <label for="exampleInputFile">Is Child</label>
                                            <div class="form-group">
                                                <select class="form-control" name="IsChild">
                                                    <option value="N">N</option>
                                                    <option value="Y">Y</option>
                                                </select>
                                            </div>
                                        </div>
                                    </div>
                                </div>
                                <div class="row">
                                    <div class="col-sm-6">
                                        <div class="form-group">
                                            <label for="exampleInputFile">Order By</label>
                                            <div class="form-group">
                                                <input type="text" class="form-control"
                                                    placeholder="Enter The order" name="order_by" id="exampleInputFile">
                                            </div>
                                        </div>

                                    </div>
                                </div>

                                <button type="button" class="btn btn-secondary AddMenu">Submit</button>
                            </form>
                        </div>
                        <div class="tab-pane fade" id="SubMenu" role="tabpanel"
                            aria-labelledby="custom-tabs-three-profile-tab">
                            <form name="menuMaster" method="post">
                                @csrf
                                <input type="hidden" name="is_sub_child" value="" />
                                <div class="card-body">
                                    <div class="row mb-3">
                                        <div class="col-sm-4">
                                            <div class="custom-control custom-radio">
                                                <input class="custom-control-input" type="radio" id="subMenuID"
                                                    name="MenusSel">
                                                <label for="subMenuID" class="custom-control-label">Sub Menu</label>
                                            </div>
                                        </div>
                                        <div class="col-sm-4">
                                            <div class="custom-control custom-radio">
                                                <input class="custom-control-input" type="radio" id="SubChildMenu"
                                                    name="MenusSel">
                                                <label for="SubChildMenu" class="custom-control-label">Sub Child
                                                    Menu</label>
                                            </div>
                                        </div>
                                    </div>
                                    <div class="row">

                                        <div class="col-sm-4">
                                            <div class="form-group">
                                                <label for="MenuName">Select Menu</label>
                                                <select class="form-control" name="menu_nm">
                                                    <option value="">Select Menu</option>

                                                </select>
                                            </div>

                                        </div>
                                        <div class="col-sm-4">
                                            <div class="form-group">
                                                <label for="routeName">Sub Menu Name</label>
                                                <input type="text" class="form-control" name="subMenuName"
                                                    id="routeName" placeholder="Menu Route">
                                            </div>

                                        </div>
                                        <div class="col-sm-4">
                                            <div class="form-group">
                                                <label for="routeName">Route Name</label>
                                                <input type="text" class="form-control" name="route" id="routeName"
                                                    placeholder="Menu Route">
                                            </div>

                                        </div>
                                        <div class="col-sm-4">

                                            <div class="form-group">
                                                <label for="exampleInputFile">Menu Icon</label>
                                                <div class="form-group">
                                                    <input type="text" class="form-control"
                                                        placeholder="Enter The Menu Icon" name="icon"
                                                        id="exampleInputFile">

                                                </div>
                                            </div>
                                        </div>
                                        <div class="col-sm-4">
                                            <div class="form-group">
                                                <label for="exampleInputFile">IsFrontEnd</label>
                                                <div class="form-group">
                                                    <select class="form-control" name="isFrontEnd">
                                                        <option value="">select</option>
                                                        <option value="Y">Y</option>
                                                        <option value="N">N</option>
                                                    </select>
                                                </div>
                                            </div>
                                        </div>
                                        <div class="col-sm-4">

                                            <div class="form-group">
                                                <label for="exampleInputFile">Front End Url</label>
                                                <div class="form-group">
                                                    <input type="text" class="form-control"
                                                        placeholder="Enter The Front End Url" name="f_url"
                                                        id="exampleInputFile">
                                                </div>
                                            </div>
                                        </div>
                                    </div>

                                    <button type="button" class="btn btn-secondary AddSubMenu">Submit</button>
                                </div>
                            </form>
                        </div>

                    </div>
                </div>

            </div>
        </div>

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
                        <div id="example1_filter" class="dataTables_filter"><label>Search:<input type="search"
                                    class="form-control form-control-sm" placeholder=""
                                    aria-controls="example1"></label>
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
                                        aria-label="Rendering engine: activate to sort column descending">Menu</th>
                                    <th class="sorting sorting_asc" tabindex="0" aria-controls="example1" rowspan="1"
                                        colspan="1" aria-sort="ascending"
                                        aria-label="Rendering engine: activate to sort column descending">Route</th>
                                    <th class="sorting sorting_asc" tabindex="0" aria-controls="example1" rowspan="1"
                                        colspan="1" aria-sort="ascending"
                                        aria-label="Rendering engine: activate to sort column descending">Icon</th>
                                    <th class="sorting sorting_asc" tabindex="0" aria-controls="example1" rowspan="1"
                                        colspan="1" aria-sort="ascending"
                                        aria-label="Rendering engine: activate to sort column descending">Status</th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                        aria-label="Browser: activate to sort column ascending">FrontEnd_Url
                                    </th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                        aria-label="Platform(s): activate to sort column ascending">Is_Child
                                    </th>  
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                    aria-label="Platform(s): activate to sort column ascending">Is_FrontEnd
                                    </th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                    aria-label="Platform(s): activate to sort column ascending">Order_By
                                    </th>
                                    <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                        aria-label="Engine version: activate to sort column ascending">Action
                                    </th>

                                </tr>
                            </thead>
                            <tbody>
                                <tr class="odd">
                                    <td colspan="4" class="dtr-control sorting_1" tabindex="0">loading</td>

                                </tr>
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
                                <li class="paginate_button page-item active"><a href="#" aria-controls="example1"
                                        data-dt-idx="1" tabindex="0" class="page-link">1</a></li>
                                <li class="paginate_button page-item "><a href="#" aria-controls="example1"
                                        data-dt-idx="2" tabindex="0" class="page-link">2</a></li>

                                <li class="paginate_button page-item next" id="example1_next"><a href="#"
                                        aria-controls="example1" data-dt-idx="7" tabindex="0" class="page-link">Next</a>
                                </li>
                            </ul>
                        </div>
                    </div>
                </div>
            </div>
        </div>


    </div>
    <div class="modal fade" id="editModal" tabindex="-1" aria-labelledby="editModalLabel" aria-hidden="true">
        <div class="modal-dialog">
            <div class="modal-content">
                <div class="modal-header">
                    <h5 class="modal-title" id="editModalLabel">Menu Master Action</h5>
                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                        <span aria-hidden="true">&times;</span>
                    </button>
                </div>
                <div class="modal-body">
                    <form id="editForm">
                        <input type="hidden" id="editId">
                        <div class="form-group">
                            <label for="editMenu">Menu</label>
                            <input type="text" class="form-control" id="editMenu" >
                        </div> 
                        <div class="form-group">
                            <label for="editRoute">Route</label>
                            <input type="text" class="form-control" id="editRoute" >
                        </div> <div class="form-group">
                            <label for="editIcon">Icon</label>
                            <input type="text" class="form-control" id="editIcon">
                        </div> <div class="form-group">
                            <label for="editStatus">Status</label>
                            <input type="text" class="form-control" id="editStatus" >
                        </div> <div class="form-group">
                            <label for="editUrl">FrontEnd_Url</label>
                            <input type="text" class="form-control" id="editUrl" >
                        </div> <div class="form-group">
                            <label for="editChild">Is_Child</label>
                            <input type="text" class="form-control" id="editChild" >
                        </div> <div class="form-group">
                            <label for="editFrontend">Is_FrontEnd</label>
                            <input type="text" class="form-control" id="editFrontend" >
                        </div> <div class="form-group">
                            <label for="editOrderBy">Order_By</label>
                            <input type="text" class="form-control" id="editOrderBy" >
                        </div>
                        <div class="form-group">
                        <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                        <button type="submit" class="btn btn-primary">Update</button>
                    </form>
                </div>
            </div>
        </div>
    </div>
</section>
<script src="{{asset('Js/MenuMaster.js')}}"></script>
@endsection