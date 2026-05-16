@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
<!-- Main content -->

<section class="content">
    <div class="card card-secondary">
        <div class="card-header">
            <h3 class="card-title">Permission Master</h3>
        </div>
        <form method="post" name="perMaster" id="permissionForm">
            <input type="hidden" value="{{ request()->cookie('Token') }}" name="apitoken">

            <div class="card-body">
                <div class="row">
                    <div class="col-sm-4">
                        <div class="form-group">
                            <label for="">Permission Name</label>
                            <div class="row">
                                <div class="col-sm-9">
                                    <input type="text" maxlength="50" name="permission" class="form-control" id="PermissionId"
                                           placeholder="Enter Permission Name">
                                </div>
                                <div class="col-sm-3">
                                    <button type="button" class="btn btn-secondary add_perm">Submit</button>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
                <div class="row">
                    <div class="col-sm-6">
                        <div class="form-group">
                            <label for="">Permission List</label>
                            <select class="form-control" name="permissionList">
                                <option value="">Select Permissions</option>
                            </select>
                        </div>
                    </div>
                    <div class="col-sm-6">
                        <label>Config List for Permission Specific</label>
                        <select class="form-control" name="configList" id="config_list">
                            <option>Select Config To Map With Permission</option>
                        </select>
                    </div>
                    <button class="btn btn-secondary mappermission" type="button">Submit</button>
                </div>
                <!-- Table to display data -->
                <div class="row mt-3">
                    <div class="col-sm-12">
                        <table class="table table-bordered" id="permissionsTable">
                            <thead>
                                <tr>
                                    <th>Permission value</th>
                                    <th>Permission key</th>
                                </tr>
                            </thead>
                            <tbody>
                                <!-- Table rows will be inserted here by JavaScript -->
                            </tbody>
                        </table>
                    </div>
                </div>
            </div>
        </form>
    </div>
</section>

<script src="{{ asset('Js/Permission.js') }}"></script>
@endsection

