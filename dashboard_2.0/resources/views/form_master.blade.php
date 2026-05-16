@extends('layout.app', ['title' => 'Form Master'])

@section('content')

<meta name="csrf-token" content="{{ csrf_token() }}">

<div class="card shadow-lg">
    <div class="card-header bg-secondary text-white">
        <h3 class="card-title">Enter Label Name and Select Option</h3>
    </div>
    <div class="card-body">
        <form id="form">
            <div class="row">
                <div class="col-md-6">
                    <div class="mb-3">
                        <label for="label_name" class="form-label">Label Name:</label>
                        <input type="text" id="label_name" name="label_name" class="form-control" placeholder="Enter label name" required>
                    </div>
                </div>
                <div class="col-md-6">
                    <div class="mb-3">
                        <label for="dropdown" class="form-label">Select an Option:</label>
                        <select id="dropdown" name="item_id" class="form-select form-control" required>
                            <option value="">Select...</option>
                        </select>
                    </div>
                </div>
            </div>
            <div class="text-center">
                <button type="submit" class="btn btn-secondary btn-lg">Submit</button>
            </div>
        </form>
    </div>
</div>


<!-- Response Area -->
<div id="response" class="mt-4"></div>

<!-- Submissions List -->
<div class="card mt-4 shadow-lg">
    <div class="card-header bg-secondary text-white">
        <h3 class="card-title">Submission List</h3>
    </div>
    <div class="card-body">
        <table class="table table-bordered">
            <thead>
                <tr>
                    <th>Label Name</th>
                    <th>Item</th>
                    <th>Actions</th>
                </tr>
            </thead>
            <tbody id="submissions-table-body">
                <!-- Submissions will be dynamically inserted here -->
            </tbody>
        </table>
    </div>
</div>



<div class="modal fade" id="editModal" tabindex="-1" aria-labelledby="editModalLabel" aria-hidden="true">
    <div class="modal-dialog">
        <div class="modal-content">
            <div class="modal-header">
                <h5 class="modal-title" id="editModalLabel">Edit Form Master</h5>
                <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                    <span aria-hidden="true">&times;</span>
                </button>
            </div>
            <div class="modal-body">
                <form id="editForm">
                    <input type="hidden" id="editId">
                    <div class="form-group">
                        <label for="editName">Label Name</label>
                        <input type="text" class="form-control" id="off_zone" name="off_zone" required>
                    </div>
                    <div class="form-group">
                        <label for="editKey">Office Name</label>
                        <input type="text" class="form-control" id="off_name" name="off_name" required>
                    </div>
                    <div class="form-group">
                        <label for="editValue">Parent Office</label>
                        <input type="text" class="form-control" id="parent_office" name="parent_office" required>
                    </div>
                    <div class="form-group">
                        <label for="editValue">Office Pincode</label>
                        <input type="text" class="form-control" id="office_pincode" name="office_pincode" required>
                    </div>
                    <div class="form-group">
                        <label for="editValue">Contact Phone</label>
                        <input type="text" class="form-control" id="contact_phone" name="contact_phone" required>
                    </div>
                    <div class="form-group">
                        <label for="editValue">Contact Email</label>
                        <input type="text" class="form-control" id="contact_email" name="contact_email" required>
                    </div>
                    <div class="form-group">
                        <label for="editValue">Address</label>
                        <input type="text" class="form-control" id="address" name="address" required>
                    </div>
                    <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                    <button type="submit" class="btn btn-primary">Update</button>
                </form>
            </div>
        </div>
    </div>
</div>



<script src="{{asset('Js\form_master.js')}}"></script>


@endsection
