@extends('layout.app', ['title' => 'Status Master'])
<!-- Main content -->
@section('content')
    @php
        $user = \Illuminate\Support\Facades\Auth::user();
    @endphp
    <!-- Main content -->
    <section class="content">

        {{-- Status Master --}}
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Status Master</h3>
            </div>
            <form method="post" name="stage_master" id="statusMasterForm">
                @csrf
                <div class="card-body">
                    <div class="row">

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Status</label>
                                <input type="text" maxlength="50" name="status_name" class="form-control"
                                    id="status_name" placeholder="Enter Status Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                    </div>

                    <button type="button" class="btn btn-secondary addBtn" id="submitBtn">Submit</button>
                </div>
            </form>
            {{-- listing for Status Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>Status Name</th>
                        <th>Created At</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>

                    @foreach ($AllStatus as $status)
                        <tr>

                            <td>{{ $status->status_name }}</td>
                            <td>{{ $status->created_at }}</td>
                            <td>

                                <button class="btn btn-sm btn-primary edit-status" data-id="{{ $status->status_id }}"
                                    data-name="{{ $status->status_name }}" data-toggle="modal"
                                    data-target="#editStatusModal">
                                    Edit
                                </button>
                                <button class="btn btn-sm btn-danger delete-status" data-id="{{ $status->status_id }}">
                                    Delete
                                </button>

                            </td>
                        </tr>
                    @endforeach


                </tbody>
            </table>



            {{-- listing data with pagination --}}

            <div class="card">


                <div class="card-body">
                    <div id="example1_wrapper" class="dataTables_wrapper dt-bootstrap4">


                        <div class="row">
                            <div class="col-sm-12 col-md-5">
                                <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1
                                    to 10 of {{ $count }} entries
                                </div>
                            </div>
                            <div class="col-sm-12 col-md-7">
                                <div class="dataTables_paginate paging_simple_numbers" id="example1_paginate">
                                    <ul class="pagination">
                                        @php
                                            $perpage = '';
                                            $i = 0;
                                            $pageCount = ceil($count / 10);
                                        @endphp
                                        <li class="paginate_button page-item previous disabled" id="example1_previous"><a
                                                href="#" aria-controls="example1" data-dt-idx="0" tabindex="0"
                                                class="page-link">Previous</a></li>
                                        @for ($i = 1; $i <= $pageCount; $i++)
                                            <li class="paginate_button page-item "><a href="?page={{ $i }}"
                                                    aria-controls="example1" data-dt-idx="1" tabindex="0"
                                                    class="page-link">{{ $i }}</a></li>
                                        @endfor

                                        <li class="paginate_button page-item next" id="example1_next"><a
                                                href="?page={{ $i = $i >= $pageCount ? $i + 1 : $i }}"
                                                aria-controls="example1" data-dt-idx="7" tabindex="0"
                                                class="page-link">Next</a>
                                        </li>
                                    </ul>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>

            </div>


        </div>

        {{-- service support system Master--}}
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Service Support Master</h3>
            </div>
            <form method="post" name="stage_master" id="sstMasterForm">
                @csrf
                <div class="card-body">
                    <div class="row">

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Service Support</label>
                                <input type="text" maxlength="50" name="service_support_type" class="form-control"
                                    id="service_support_type" placeholder="Enter Status Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                    </div>

                    <button type="button" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>
            {{-- listing for SST Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>Service Support Type</th>
                        <th>Created At</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>
                    @foreach ($AllSst as $AllSst)
                        <tr>

                            <td>{{ $AllSst->service_support_type }}</td>
                            <td>{{ $AllSst->created_at }}</td>
                            <td>


                                <button class="btn btn-sm btn-primary edit-sst" data-id="{{ $AllSst->sst_id }}"
                                    data-name="{{ $AllSst->service_support_type }}" data-toggle="modal"
                                    data-target="#editSstModal">
                                    Edit
                                </button>
                                <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $AllSst->sst_id }}">
                                    Delete
                                </button>

                            </td>
                        </tr>
                    @endforeach
                </tbody>
            </table>

            <!-- Edit SST Modal -->
            <div class="modal fade" id="editSstModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Service Support Type</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editSstForm">
                                @csrf
                                <input type="hidden" name="id" id="edit_sst_id">
                                <div class="form-group">
                                    <label for="service_support_type">Service Support Type</label>
                                    <input type="text" class="form-control" id="edit_sst_name"
                                        name="service_support_type">
                                </div>
                                <button type="submit" class="btn btn-primary">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>


        </div>

        {{-- Section Master--}}
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Section Master</h3>
            </div>
            <form method="post" name="stage_master" id="sectionForm">
                @csrf
                <div class="card-body">
                    <div class="row">
                        <div class="col-sm-6">

                            <div class="form-group">
                                <label for="">LOB</label>
                                <select name="lob" class="custom-select" id="fetchLob">
                                    <option value="">Please Select LOB</option>
                                </select>

                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>


                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Service Support</label>
                                <select name="service_support_type" class="custom-select">
                                    <option value="">Please Select Service Support Type</option>
                                    @foreach ($sst as $item)
                                        <option value="{{ $item->service_support_type }}">
                                            {{ $item->service_support_type }}</option>
                                    @endforeach
                                </select>
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Section</label>
                                <input type="text" maxlength="50" name="section_name" class="form-control"
                                    id="section_name" placeholder="Enter Section Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>


                    </div>

                    <button type="button" class="btn btn-secondary addBtn" id="submitBtnSection">Submit</button>
                </div>
            </form>
            {{-- listing for Section Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>LOB</th>
                        <th>Service Support Type</th>
                        <th>Section Name</th>
                        <th>Created At</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>
                    @foreach ($AllSection as $value)
                        <tr>
                            <td>{{ $value->lob }}</td>
                            <td>{{ $value->service_support_type }}</td>
                            <td>{{ $value->section_name }}</td>
                            <td>{{ $value->created_at }}</td>
                            <td>



                                <button class="btn btn-sm btn-primary edit-section" data-id="{{ $value->section_id }}"
                                    data-name="{{ $value->section_name }}"
                                    data-key ="{{ $value->service_support_type }}" data-value="{{ $value->lob }}"
                                    data-toggle="modal" data-target="#editSectionModal">
                                    Edit
                                </button>
                                <button class="btn btn-sm btn-danger delete-section" data-id="{{ $value->section_id }}">
                                    Delete
                                </button>

                            </td>
                        </tr>
                    @endforeach
                </tbody>
            </table>



            <!-- Edit SST Modal -->
            <div class="modal fade" id="editSstModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Service Support Type</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editSstForm">
                                @csrf
                                <input type="hidden" name="id" id="edit_sst_id">
                                <div class="form-group">
                                    <label for="service_support_type">Service Support Type</label>
                                    <input type="text" class="form-control" id="edit_sst_name"
                                        name="service_support_type">
                                </div>
                                <button type="submit" class="btn btn-primary">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

        </div>

        {{-- Section Feild Master--}}
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Section Field Master</h3>
            </div>
            <form method="post" name="stage_master" id="fieldForm">
                @csrf
                <div class="card-body">
                    <div class="row">
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">LOB</label>
                                <select name="lob" class="custom-select" id="lobDropdown">
                                    <option value="">Please Select LOB</option>
                                </select>

                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>


                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Service Support</label>
                                <select name="service_support_type" class="custom-select">
                                    <option value="">Please Select Service Support Type</option>
                                    @foreach ($sst as $item)
                                        <option value="{{ $item->service_support_type }}">
                                            {{ $item->service_support_type }}</option>
                                    @endforeach
                                </select>
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Section</label>
                                <select name="section_name" class="custom-select">
                                    <option value="">Please Select Section</option>
                                    @foreach ($section as $item)
                                        <option value="{{ $item->section_name }}">{{ $item->section_name }}</option>
                                    @endforeach
                                </select>
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Section Feild</label>
                                <input type="text" maxlength="50" name="section_field_name" class="form-control"
                                    id="section_field_name" placeholder="Enter Section Field Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>


                    </div>

                    <button type="button" class="btn btn-secondary addBtn" id="submitBtnField">Submit</button>
                </div>
            </form>
            {{-- listing for Section Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>LOB</th>
                        <th>Service Support Type</th>
                        <th>Section Name</th>
                        <th>Section Feild Name</th>
                        <th>Created At</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>
                    @foreach ($AllField as $key)
                        <tr>
                            <td>{{ $key->lob }}</td>
                            <td>{{ $key->service_support_type }}</td>
                            <td>{{ $key->section_name }}</td>
                            <td>{{ $key->section_field_name }}</td>
                            <td>{{ $key->created_at }}</td>
                            <td>


                                <button class="btn btn-sm btn-primary edit-section-field" data-id="{{ $key->field_id }}"
                                    data-name="{{ $key->lob }}" data-key="{{ $key->service_support_type }}"
                                    data-value="{{ $key->section_name }}"
                                    data-feild="{{ $key->section_field_name }}"data-toggle="modal"
                                    data-target="#editFieldModal">
                                    Edit
                                </button>
                                <button class="btn btn-sm btn-danger delete-field" data-id="{{ $key->field_id }}">
                                    Delete
                                </button>

                            </td>
                        </tr>
                    @endforeach
                </tbody>
            </table>

            <!-- Edit Status Modal -->
            <div class="modal fade" id="editStatusModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Status</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editStatusForm">
                                @csrf
                                <input type="hidden" name="id" id="edit_status_id">
                                <div class="form-group">
                                    <label for="status_name">Status Name</label>
                                    <input type="text" class="form-control" id="edit_status_name" name="status_name">
                                </div>
                                <button type="submit" class="btn btn-primary">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Edit SST Modal -->
            <div class="modal fade" id="editSstModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Service Support Type</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editSstForm">
                                @csrf
                                <input type="hidden" name="id" id="edit_sst_id">
                                <div class="form-group">
                                    <label for="service_support_type">Service Support Type</label>
                                    <input type="text" class="form-control" id="edit_sst_name"
                                        name="service_support_type">
                                </div>
                                <button type="submit" class="btn btn-primary">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Edit Section Modal -->
            <div class="modal fade" id="editSectionModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Section</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editSectionForm">
                                @csrf
                                <input type="hidden" id="section_master_id">
                                <div class="form-group">
                                    <label for="lob">LOB</label>

                                    <select name="lob" class="form-control" id="edit_lob">
                                        <option value="">Select LOB</option>
                                        @foreach ($fetchLob as $tag)
                                            <option value="{{ $tag->lob_name }}">{{ $tag->lob_name }}</option>
                                        @endforeach
                                    </select>


                                </div>

                                <div class="form-group">
                                    <label for="service_support_type">Service Support Type</label>

                                        <select name="service_support_type" class="custom-select" id="edit_service_support_type">
                                            <option value="">Please Select Service Support Type</option>
                                            @foreach ($sst as $item)
                                                <option value="{{ $item->service_support_type }}">
                                                    {{ $item->service_support_type }}</option>
                                            @endforeach
                                        </select>
                                </div>

                                <div class="form-group">
                                    <label for="section_name">Section</label>
                                    <input type="text" class="form-control" id="edit_section_name"
                                        name="section_name">
                                </div>
                                <button type="submit" class="btn btn-primary ">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Edit Field Modal -->
            <div class="modal fade" id="editfieldModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Section</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editfieldForm">
                                @csrf
                                <input type="hidden" id="field_master_id">
                                <div class="form-group">
                                    <label for="lob">LOB</label>

                                    <select name="lob" class="form-control" id="field_master_lob">
                                        <option value="">Select Tag</option>
                                        @foreach ($fetchLob as $tag)
                                            <option value="{{ $tag->lob_name }}">{{ $tag->lob_name }}</option>
                                        @endforeach
                                    </select>

                                </div>

                                <div class="form-group">
                                    <label for="service_support_type">Service Support Type</label>

                                        <select name="service_support_type" class="custom-select" id="field_master_sst">
                                            <option value="">Please Select Service Support Type</option>
                                            @foreach ($sst as $item)
                                                <option value="{{ $item->service_support_type }}">
                                                    {{ $item->service_support_type }}</option>
                                            @endforeach
                                        </select>
                                </div>

                                <div class="form-group">
                                    <label for="section_name">Section</label>

                                        <select name="section_name" class="custom-select" id="field_master_section">
                                            <option value="">Please Select Section</option>
                                            @foreach ($section as $item)
                                                <option value="{{ $item->section_name }}">{{ $item->section_name }}</option>
                                            @endforeach
                                        </select>
                                </div>
                                <div class="form-group">
                                    <label for="section_field_name">Feild</label>
                                    <input type="text" class="form-control" id="field_master_field"
                                        name="section_field_name">
                                </div>
                                <button type="submit" class="btn btn-primary ">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

        </div>


    </section>
    <meta name="csrf-token" content="{{ csrf_token() }}">
    <script src="{{ asset('Js/endorsement.js') }}"></script>

    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
