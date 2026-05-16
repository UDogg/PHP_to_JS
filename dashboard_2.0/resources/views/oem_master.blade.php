@extends('layout.app', ['title' => 'Status Master'])
<!-- Main content -->
@section('content')
    @php
        $user = \Illuminate\Support\Facades\Auth::user();
    @endphp
    <!-- Main content -->
    <section class="content">


        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">OEM Master</h3>
            </div>

            <form method="post" name="stage_master" id="sstMasterForm" enctype="multipart/form-data">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">
                    <div class="row">

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">OEM Name</label>
                                <input type="text" maxlength="50" name="oem_name" class="form-control"
                                    id="oem_name" placeholder="Enter OEM Name">

                            </div>
                        </div>


                    </div>

                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>

        </div>
        {{-- MIS Onboarding ----}}
        <div class="card card-secondary"  id="misOnboardingSection" style="display: none;">
            <div class="card-header">
                <h3 class="card-title">MIS Onboarding</h3>
            </div>

            <form method="post" name="oem_master" id="oemMasterForm" enctype="multipart/form-data">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">
                    <div class="row">

                        <div class="col-md-6">
                            <label for="misp_name" class = "required">Add MISP Name</label>
                            <input type="text" class="form-control" id="misp_name" name="misp_name" required>
                        </div>

                        <div class="col-md-6">
                            <label for="oem_name" class="required">Add OEM Name</label>
                            <select id="oem_name" name="oem_name" class="form-control" required>
                                <option value="" {{ old('oem_name') == '' ? 'selected' : '' }}>
                                    Select OEM Name
                                </option>
                                @foreach ($oem_data as $oem)
                                    <option value="{{ $oem->oem_name }}" {{ old('oem_name') == $oem->oem_name ? 'selected' : '' }}>
                                        {{ $oem->oem_name }}
                                    </option>
                                @endforeach
                            </select>
                        </div>
                    </div>
                    <div class="row">
                        <div class="col-md-6">
                            <label for="pan_number" class="required">PAN Number</label>
                            <input type="text" class="form-control" id="pan_number" name="pan_number" required>
                        </div>

                        <div class="col-md-6">
                            <label for="zone" >Zone</label>
                            <input type="text" class="form-control" id="zone" placeholder="Enter zone" name="redirection_url" value="{{ old('zone') }}">
                        </div>
                    </div>

                    <div class="row">
                        <div class="col-md-6">
                            <label for="gstin" class="required">GSTIN</label>
                            <input type="text" class="form-control" id="gstin" placeholder="Enter GSTIN Number" name="gstin" required>
                        </div>

                        <div class="col-md-6">
                            <label for="dealer_code" >Dealer Code</label>
                            <input type="text" class="form-control" id="dealer_code" placeholder="Enter Dealer Code" name="dealer_code" value="{{ old('dealer_code') }}">
                        </div>
                    </div>

                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                    {{-- @if($oem_data->isNotEmpty())
                        @php $firstOem = $oem_data->first(); @endphp
                        <button type="submit" class="btn btn-secondary addBtn" id="submitBtn"
                            data-id="{{ $firstOem->id }}"
                            data-oem-name="{{ $firstOem->oem_name }}"
                            data-misp-name="{{ $firstOem->misp_name }}"
                            data-pan-number="{{ $firstOem->pan_number }}"
                            data-zone="{{ $firstOem->zone }}"
                            data-gstin="{{ $firstOem->gstin }}"
                            data-dealer-code="{{ $firstOem->dealer_code }}">Submit</button>
                    @endif --}}

                </div>
            </form>


        </div>

        {{-- Add Branch ----}}
        <div class="card card-secondary"  id="branchSection" style="display: none;">
            <div class="card-header">
                <h3 class="card-title">Branch Details</h3>
            </div>

            <form method="post" name="oem_master" id="branchForm" enctype="multipart/form-data">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">
                    <div class="row">

                        <div class="col-md-6">
                            <label for="branch_name" class = "required">Add HO/Branch</label>
                            <input type="text" class="form-control" id="branch_name" name="branch_name" required>
                        </div>

                        <div class="col-md-6">
                            <label for="oem_name" class="required">Address</label>

                            <textarea class="form-control" id="address" name="address"></textarea>
                        </div>
                    </div>


                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>


            <!-- Edit Field Modal -->
            {{-- <div class="modal fade" id="editfieldModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit OEM Data</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">

                            <form id="editfieldForm">
                                @csrf
                                <input type="hidden" id="field_master_id">
                                <div class="form-group">
                                    <label for="editLobMasterData" class="required">OEM Master</label>
                                    <select id="field_master_lob" name="lobMasterData" class="form-control" required>
                                        <option value="" disabled>Select OEM Master</option>
                                        @foreach ($get_oem_name as $oem_data)
                                            <option value="{{ $oem_data->oem_name }}">{{ $oem_data->oem_name }}</option>
                                        @endforeach

                                    </select>
                                </div>
                                <div class="form-group">
                                    <label for="misp_name" class = "required">Add MISP Name</label>
                                    <input type="text" class="form-control" id="field_master_sst" name="misp_name" required>
                                </div>

                                    <div class="form-group">
                                        <label for="pan_number" class="required">PAN Number</label>
                                        <input type="text" class="form-control" id="field_master_section" name="pan_number" required>
                                    </div>

                                    <div class="form-group">
                                        <label for="zone" >Zone</label>
                                        <input type="text" class="form-control" id="field_master_url" placeholder="Enter zone" name="redirection_url" value="{{ old('zone') }}">
                                    </div>


                                    <div class="form-group">
                                        <label for="gstin" class="required">GSTIN</label>
                                        <input type="text" class="form-control" id="field_master_field" placeholder="Enter GSTIN Number" name="gstin" required>
                                    </div>

                                    <div class="form-group">
                                        <label for="dealer_code" >Dealer Code</label>
                                        <input type="text" class="form-control" id="field_master_logo" placeholder="Enter Dealer Code" name="dealer_code" value="{{ old('dealer_code') }}">
                                    </div>



                                <button type="submit" class="btn btn-primary ">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div> --}}
        </div>
            {{-- listing for SST Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>OEM Name</th>
                        <th>MISP Name</th>
                        <th>Pan Number</th>
                        <th>GSTIN</th>
                        <th>Zone</th>
                        <th>Dealer Code</th>
                        <th>Branch Name</th>
                        <th>Address</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>

                    @foreach ($oem_data as $oem_data)
                    {{-- {{dd($oem_data)}} --}}
                        <tr>

                            <td>{{ $oem_data->oem_name }}</td>
                            <td>{{ $oem_data->misp_name }}</td>
                            <td>{{ $oem_data->pan_number }}</td>
                            <td>{{ $oem_data->gstin }}</td>
                            <td>{{ $oem_data->zone }}</td>
                            <td>{{ $oem_data->dealer_code }}</td>
                            <td>{{ $oem_data->branch_name }}</td>
                            <td>{{ $oem_data->address }}</td>

                            <td>


                                <button class="btn btn-sm btn-primary edit-section-field"
                                    data-id="{{ $oem_data->id }}"
                                    data-name="{{  $oem_data->oem_name }}"
                                    data-key="{{ $oem_data->misp_name }}"
                                    data-value="{{ $oem_data->pan_number }}"
                                    data-feild="{{ $oem_data->gstin }}"
                                    data-url="{{ $oem_data->zone }}"
                                    data-logo="{{ $oem_data->dealer_code }}"
                                    data-enabled="{{ $oem_data->branch_name }}"
                                    data-disabled="{{ $oem_data->address }}"
                                    data-toggle="modal"
                                    data-target="#editFieldModal">
                                    Edit
                                </button>
                                <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $oem_data->id }}">
                                    Delete
                                </button>


                            </td>
                        </tr>
                    @endforeach
                </tbody>
            </table>


    </section>

    {{-- MIS Onboarding Modal ----}}




    <meta name="csrf-token" content="{{ csrf_token() }}">
    <script src="{{ asset('Js/oem_master.js') }}"></script>

    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
