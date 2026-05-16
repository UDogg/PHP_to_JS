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
                <h3 class="card-title">LOB Data Master</h3>
            </div>

            <form method="post" name="stage_master" id="sstMasterForm" enctype="multipart/form-data">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">
                    <div class="row">

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Lob Name</label>
                                <input type="text" maxlength="50" name="lob_name" class="form-control"
                                    id="lob_name" placeholder="Enter Status Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Lob</label>
                                <input type="text" maxlength="50" name="lob" class="form-control"
                                    id="lob" placeholder="Enter Lob">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                    </div>

                    <div class="row">

                        <div class="col-sm-6">

                            <div class="form-group">
                                <label for="is_enabled">Add Is Enabled</label>
                                <select name="is_enabled" class="form-control" id="is_enabled" required>
                                    <option value="">Select Status</option>
                                    <option value="Y" {{ old('is_enabled') == 'Y' ? 'selected' : '' }}>Yes</option>
                                    <option value="N" {{ old('is_enabled') == 'N' ? 'selected' : '' }}>No</option>
                                </select>
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>

                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Frontend Url</label>
                                <input type="text" maxlength="50" name="frontend_url" class="form-control"
                                    id="frontend_url" placeholder="Enter Frontend Url">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                    </div>

                    <div class="row">

                        <div class="col-md-6">
                            <div class="form-group">
                                <label for="lob_icon" class = "required">Add Lob Icon</label>
                                <input type="file" class="form-control" id="lob_icon"
                                    name="lob_icon" value="{{ old('lob_icon') }}" required>
                            </div>
                        </div>
                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Lob Master Name</label>
                                <input type="text" maxlength="50" name="lob_master_name" class="form-control"
                                    id="lob_master_name" placeholder="Enter Lob Master Name">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Customer Frontend Url</label>
                                <input type="text" maxlength="50" name="customer_frontend_url" class="form-control"
                                    id="customer_frontend_url" placeholder="Enter Customer Frontend Url">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                        <div class="col-sm-6">
                            <div class="form-group">
                                <label for="">Add Payment Url</label>
                                <input type="text" maxlength="50" name="payment_url" class="form-control"
                                    id="payment_url" placeholder="Enter Pyment Url">
                                <input type="hidden" name="is_update" value="">
                                <input type="hidden" name="id" value="">
                            </div>
                        </div>

                    </div>

                    <div class="row">

                    </div>

                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>

            {{-- listing for SST Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>Lob Name</th>
                        <th>Lob</th>
                        <th>Is Enabled</th>
                        <th>Frontend Url</th>
                        <th>Payment Url</th>
                        <th>Customer Frontend Url</th>
                        <th>Lob Icon</th>
                        <th>Lob Master Name</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>
                    @foreach ($lobs as $company)

                        <tr>

                            <td>{{ $company->lob_name }}</td>
                            <td>{{ $company->lob }}</td>
                            <td>{{ $company->is_enabled }}</td>
                            <td>{{ $company->frontend_url }}</td>
                            <td>{{ $company->payment_url }}</td>
                            <td>{{ $company->customer_frontend_url }}</td>
                            <td>{{ $company->lob_icon }}</td>
                            <td>{{ $company->lob_master_name }}</td>

                            <td>


                                <button class="btn btn-sm btn-primary edit-section-field"
                                    data-id="{{ $company->id }}"
                                    data-name="{{ $company->lob_name }}"
                                    data-key="{{ $company->lob }}"
                                    data-enabled="{{ $company->is_enabled }}"
                                    data-frontend_url="{{ $company->frontend_url }}"
                                    data-customer_frontend_url="{{ $company->customer_frontend_url }}"
                                    data-lob_icon="{{ $company->lob_icon }}"
                                    data-lob_master_name="{{ $company->lob_master_name }}"
                                    data-payment_url="{{ $company->payment_url }}"
                                    data-toggle="modal"
                                    data-target="#editfieldModal">
                                    Edit
                                </button>


                            </td>
                        </tr>
                    @endforeach
                </tbody>
            </table>

            <!-- Edit Field Modal -->
            <div class="modal fade" id="editfieldModal" tabindex="-1" role="dialog" aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title">Edit LOB Master Data</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close"><span>&times;</span></button>
                        </div>
                        <div class="modal-body">
                            <form id="editfieldForm" enctype="multipart/form-data">
                                @csrf
                                <input type="hidden" id="field_master_id" name="id">
            
                                <div class="form-group">
                                    <label for="lob_name">LOB Name</label>
                                    <input type="text" class="form-control" id="field_master_lob" name="lob_name" required>
                                </div>
            
                                <div class="form-group">
                                    <label for="lob">LOB</label>
                                    <input type="text" class="form-control" id="field_master_sst" name="lob" readonly>
                                </div>
            
                                <div class="form-group">
                                    <label for="is_enabled">Is Enabled</label>
                                    <select name="is_enabled" class="form-control" id="is_enabled" required>
                                        <option value="Y">Yes</option>
                                        <option value="N">No</option>
                                    </select>
                                </div>
            
                                <div class="form-group">
                                    <label for="frontend_url">Frontend URL</label>
                                    <input type="text" class="form-control" id="field_master_field" name="frontend_url" required>
                                </div>

                                <div class="form-group">
                                    <label for="payment_url">Payment Url</label>
                                    <input type="text" class="form-control" id="field_master_field_payment_url" name="payment_url" >
                                </div>

                                <div class="form-group">
                                    <label for="field_master_field_cust_url">Customer Frontend URL</label>
                                    <input type="text" class="form-control" id="field_master_field_cust_url" name="customer_frontend_url" >
                                </div>
            
                                <div class="form-group">
                                    <label for="lob_icon">LOB Icon</label>
                                    <input type="file" class="form-control" id="field_master_logo" name="lob_icon" accept="image/*">
                                    <small id="currentLogoText" class="form-text text-muted"></small>
                                </div>
            
                                <div class="form-group">
                                    <label for="lob_master_name">LOB Master Name</label>
                                    <input type="text" class="form-control" id="field_master_name" name="lob_master_name" required>
                                </div>
            
                                <button type="submit" class="btn btn-primary">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>
            


        </div>




    </section>
    <meta name="csrf-token" content="{{ csrf_token() }}">
    <script src="{{ asset('Js/lob_master.js') }}"></script>

    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
