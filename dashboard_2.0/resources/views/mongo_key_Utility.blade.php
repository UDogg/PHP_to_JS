@extends('layout.app', ['title' => 'Mongo Key Utility'])

@section('content')

<style>
    .pagination {
        font-size: 14px;
        justify-content: center;
    }
    </style>

<meta name="csrf-token" content="{{ csrf_token() }}">

<section class="content">


    <div class="card">
        <div class="card-header">
            <h3>Mongo Key Utility List</h3>
            <!-- ADD BUTTON -->
    <button class="btn btn-dark float-right mb-3" data-toggle="modal" data-target="#addModal">
        ADD <i class="fa-solid fa-plus"></i>
    </button>
        </div>

        <div class="card-body">
            <table class="table table-bordered">
                <thead>
                    <tr>
                        <th>#</th>
                        <th>Mongo Field Name</th>
                        <th>Is Default</th>
                        <th>Is Visible</th>
                        <th>Action</th>
                    </tr>
                </thead>

                <tbody>
                    @foreach($policy_status_columns as $index => $value)
                    <tr>
                        <td>{{ $loop->iteration }}</td>
                        <td>{{ $value->column_name }}</td>
                        <td>{{ $value->is_default }}</td>
                        <td>{{ $value->is_visible }}</td>
                        <td>
                            <button class="btn btn-sm btn-primary editBtn" data-id="{{ $value->id }}">Edit</button>
                            <button class="btn btn-sm btn-danger deleteBtn" data-id="{{ $value->id }}">Delete</button>
                        </td>
                    </tr>
                    @endforeach
                </tbody>
            </table>

            {{ $policy_status_columns->links('pagination::bootstrap-4') }}
        </div>
    </div>

</section>

<!-- ================= ADD MODAL ================= -->
<div class="modal fade" id="addModal">
    <div class="modal-dialog modal-lg">
        <form id="addForm" class="modal-content">
            @csrf
            <div class="modal-header">
                <h5>Add Mongo Key</h5>
                <button type="button" class="close" data-dismiss="modal">&times;</button>
            </div>

            <div class="modal-body">

                <input type="text" name="column_name" class="form-control mb-2" placeholder="Column Name" required>

                <select name="is_default" class="form-control mb-2">
                    <option value="Y">Default - Yes</option>
                    <option value="N">Default - No</option>
                </select>

                <select name="is_visible" class="form-control mb-2">
                    <option value="Y">Visible - Yes</option>
                    <option value="N">Visible - No</option>
                </select>
            </div>

            <div class="modal-footer">
                <button class="btn btn-success">Save</button>
            </div>
        </form>
    </div>
</div>

<!-- ================= EDIT MODAL ================= -->
<div class="modal fade" id="editModal">
    <div class="modal-dialog modal-lg">
        <form id="editForm" class="modal-content">
            @csrf
            <input type="hidden" id="edit_id">

            <div class="modal-header">
                <h5>Edit Mongo Key</h5>
                <button type="button" class="close" data-dismiss="modal">&times;</button>
            </div>

            <div class="modal-body">

                <input type="text" id="edit_column_name" class="form-control mb-2" required>

                <select id="edit_is_default" class="form-control mb-2">
                    <option value="Y">Default - Yes</option>
                    <option value="N">Default - No</option>
                </select>

                <select id="edit_is_visible" class="form-control mb-2">
                    <option value="Y">Visible - Yes</option>
                    <option value="N">Visible - No</option>
                </select>
            </div>

            <div class="modal-footer">
                <button class="btn btn-primary">Update</button>
            </div>
        </form>
    </div>
</div>

<script src="{{ asset('Js/mongoKeyUtility.js') }}"></script>

@endsection