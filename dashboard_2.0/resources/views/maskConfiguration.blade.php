@extends('layout.app', ['title' => 'Status Master'])
<!-- Main content -->
@section('content')
    {{-- @php
        $user = \Illuminate\Support\Facades\Auth::user();
    @endphp --}}
    <!-- Main content -->
    <section class="content">
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Mask configuration</h3>
            </div>
            <form method="post" name="stage_master" id="sstMasterForm">
                @csrf
                <div class="card-body">
                    <div class="row">

                        
                        
                        
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Key Name</label>
                                <input type="text" maxlength="50" name="key_name" class="form-control"
                                    id="key_name" placeholder="Enter Key Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Masking position</label>
                                <input type="text" maxlength="50" name="masking_position" class="form-control"
                                    id="masking_position" placeholder="Enter Key Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>
                    </div>

                    <div class="row">
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Masking symbol</label>
                                <input type="text" maxlength="50" name="masking_symbol" class="form-control"
                                    id="masking_symbol" placeholder="Enter Key Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-sm-6">
                        </div>

                    </div>
                    <button type="button" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>
            <table class="table">
                <thead>
                    <tr>
                        
                        <th>key Name</th>
                        <th>Masking Position</th>
                        <th>Masking Symbol</th>
                        <th>For Report</th>
                        <th>Status</th>
                        <th>Created At</th>
                        <th>Updated At</th>
                        <th>Actions</th>
                       
                    </tr>
                </thead>
                <tbody>
                    @foreach ($maskConfigurator as $maskConfigurator)

                        <tr>

                            <td>{{ $maskConfigurator->key_name }}</td>
                            <td>{{ $maskConfigurator->masking_position }}</td>
                            <td>{{ $maskConfigurator->masking_symbol }}</td>
                            <td>{{ $maskConfigurator->for_report }}</td>
                            <td>{{ $maskConfigurator->status }}</td>
                            <td>{{ $maskConfigurator->created_at }}</td>
                            <td>{{ $maskConfigurator->updated_at }}</td>
                            <td>


                                {{-- <button class="btn btn-sm btn-primary edit-section-field"
                                    data-id="{{ $company->company_id }}"
                                    data-name="{{  $company->company_name }}"
                                    data-key="{{ $company->company_shortname }}"
                                    data-value="{{ $company->health_alias }}"
                                    data-feild="{{ $company->motor_alias }}"
                                    data-url="{{ $company->url }}"
                                    data-logo="{{ $company->logo }}"
                                    data-is_renewal="{{ $company->is_renewal }} "
                                    data-is_renewal_bike="{{ $company->is_renewal_bike }}" data-toggle="modal"
                                    data-target="#editFieldModal">
                                    Edit
                                </button> --}}
                                <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $maskConfigurator->id }}">
                                    Delete
                                </button>

                            </td>
                        </tr>
                    @endforeach
                </tbody>
            </table>

            <!-- Edit Field Modal -->
            {{-- <div class="modal fade" id="editfieldModal" tabindex="-1" role="dialog"
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
                                    <label for="company_name">Company Name</label>
                                    <input type="text" class="form-control" id="field_master_lob" name="company_name">
                                </div>

                                <div class="form-group">
                                    <label for="company_shortname">company_shortname</label>
                                    <input type="text" class="form-control" id="field_master_sst"
                                        name="company_shortname">
                                </div>

                                <div class="form-group">
                                    <label for="health_alias">health_alias</label>
                                    <input type="text" class="form-control" id="field_master_section"
                                        name="health_alias">
                                </div>
                                <div class="form-group">
                                    <label for="motor_alias">motor_alias</label>
                                    <input type="text" class="form-control" id="field_master_field"
                                        name="motor_alias">
                                </div>
                                <div class="form-group">
                                    <label for="url">url</label>
                                    <input type="text" class="form-control" id="field_master_url"
                                        name="url">
                                </div>
                                <div class="form-group">
                                    <label for="logo">logo</label>
                                    <input type="text" class="form-control" id="field_master_logo"
                                        name="logo">
                                </div>
                                <div class="form-group">
                                    <label for="is_renewal">is_renewal</label>
                                    <input type="text" class="form-control" id="field_master_is_renewal"
                                        name="is_renewal">
                                </div>
                                <div class="form-group">
                                    <label for="is_renewal_bike">is_renewal_bike</label>
                                    <input type="text" class="form-control" id="field_master_is_renewal_bike"
                                        name="is_renewal_bike">
                                </div>
                                <button type="submit" class="btn btn-primary ">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div> --}}
        </div>
    </section>
    <meta name="csrf-token" content="{{ csrf_token() }}">
    <script src="{{ asset('Js/maskConfiguration.js') }}"></script>
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
