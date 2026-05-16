@extends('layout.app', ['pageTitle' => 'Company Master', 'pageHeader' => 'Company Master', 'menu' => 'CompanyMaster', 'subMenu' => 'CompanyMaster']);
<!-- Main content -->
<head>
    <meta name="csrf-token" content="{{ csrf_token() }}">
</head>
@section('content')
    @php
        $user = \Illuminate\Support\Facades\Auth::user();
    @endphp
    <!-- Main content -->
    <section class="content">


        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Compnay Master</h3>
            </div>
            <form method="post" name="stage_master" id="sstMasterForm" enctype="multipart/form-data">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">
                    <div class="row">
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="lobname">LOB NAME</label>
                                <select type="text" class="form-control" id="lobname" name="lobname" required>
                                    <option value="" disabled selected>Select</option>
                                    <option value="HEALTH" {{ old('lobname') == 'HEALTH' ? 'selected' : '' }}>HEALTH</option>
                                    <option value="MOTOR" {{ old('lobname') == 'MOTOR' ? 'selected' : '' }}>MOTOR</option>
                                </select>
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Company Name</label>
                                <input type="text" maxlength="50" name="company_name" class="form-control"
                                    id="company_name" placeholder="Enter Status Name" required>
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Company Shortname</label>
                                <input type="text" maxlength="50" name="company_shortname" class="form-control"
                                    id="company_shortname" placeholder="Enter Shortname">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-md-6">
                            <div class="form-group">
                                <label for="logo">Add Logo</label>
                                <input type="file" class="form-control" id="logo"
                                    name="logo" value="{{ old('logo') }}">
                            </div>
                        </div>


                    </div>


                    <div class="row">

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="live_insu_company">Live Insurance Company</label>
                                <select name="live_insu_company" class="form-control" id="live_insu_company">
                                    <option value="" disabled selected>Select</option>
                                    <option value="Y" {{ old('live_insu_company') == 'Y' ? 'selected' : '' }}>Yes</option>
                                    <option value="N" {{ old('live_insu_company') == 'N' ? 'selected' : '' }}>No</option>
                                </select>
                            </div>
                        </div>

                    </div>

                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>
            {{-- listing for SST Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>Lob</th>
                        <th>Company Name</th>
                        <th>Company Shortname</th>
                        <th>logo</th>
                        <th>Live Insurance Company</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>

                    @if(isset($company_data) && count($company_data) > 0)
                        @foreach ($company_data as $company)
                            <tr>
                                <td>{{ $company->lobname }}</td>
                                <td>{{ $company->company_name }}</td>
                                <td>{{ $company->company_shortname }}</td>
                                <td>{{ $company->logo }}</td>
                                <td>{{ $company->live_insu_company }}</td>
                                <td>
                                    <button class="btn btn-sm btn-primary edit-section-field"
                                        data-id="{{ $company->company_id }}"
                                        data-lobname="{{ $company->lobname }}"
                                        data-name="{{  $company->company_name }}"
                                        data-key="{{ $company->company_shortname }}"
                                        data-logo="{{ $company->logo }}"
                                        data-live_insu_company="{{ $company->live_insu_company }}"
                                        data-toggle="modal"
                                        data-target="#editFieldModal">
                                        Edit
                                    </button>
                                    <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $company->company_id }}">
                                        Delete
                                    </button>
                                </td>
                            </tr>
                        @endforeach
                    @else
                        <tr>
                            <td colspan="9" class="text-center">No company data available.</td>
                        </tr>
                    @endif



                </tbody>
            </table>

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
                                    <label for="lobname">LOB</label>
                                    <select type="text" class="form-control" id="lob_name" name="lobname" required>
                                        <option value="" disabled {{ old('lobname') ? '' : 'selected' }}>Select</option>
                                        <option value="HEALTH" {{ old('lobname') == 'HEALTH' ? 'selected' : '' }}>HEALTH</option>
                                        <option value="MOTOR" {{ old('lobname') == 'MOTOR' ? 'selected' : '' }}>MOTOR</option>
                                    </select>
                                </div>
                                <div class="form-group">
                                    <label for="company_name">Company Name</label>
                                    <input type="text" class="form-control" id="field_master_companyName" name="company_name" required>
                                </div>

                                <div class="form-group">
                                    <label for="company_shortname">Company Shortname</label>
                                    <input type="text" class="form-control" id="field_master_sst" name="company_shortname">
                                </div>
                               
                                <div class="form-group">
                                    <label for="logo">Logo</label>
                                    <input type="file" class="form-control" id="field_master_logo" name="logo">
                                    
                                    <div id="logoPreviewContainer" class="mt-2" style="display:none;">
                                        <img id="logoPreview" src="" alt="Logo Preview" width="100" class="d-block">
                                    </div>
                                
                                    <input type="hidden" id="field_master_old_logo" name="old_logo" value="">
                                    <div id="removeLogoContainer" class="mt-2" style="display:none;">
                                        <div class="form-check">
                                            <input class="form-check-input" type="checkbox" id="remove_logo" name="remove_logo" value="1">
                                            <label class="form-check-label" for="remove_logo">Remove Logo</label>
                                        </div>
                                    </div>
                                </div>
                                <div id="logoPreviewContainer" class="mb-2">
                                    <img id="logoPreview" src="" alt="Logo Preview" width="100" class="d-block" style="display: none;">
                                </div>
                                

                                <div class="form-group">
                                    <label for="live_insu_company">Live Insurance Company</label>
                                    <select name="live_insu_company" class="form-control" id="live_insu_companyflag" required>
                                        <option value="" disabled {{ old('live_insu_company') ? '' : 'selected' }}>Select</option>
                                        <option value="Y" {{ old('live_insu_company') == 'Y' ? 'selected' : '' }}>Yes</option>
                                        <option value="N" {{ old('live_insu_company') == 'N' ? 'selected' : '' }}>No</option>
                                    </select>
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
    <script src="{{ asset('Js/company_master.js') }}"></script>

    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
