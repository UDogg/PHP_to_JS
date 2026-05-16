@extends('layout.app', ['title' => 'visibility_report'])
<!-- Main content -->
@section('content')
<!-- Main content -->

<link rel="stylesheet" href="{{asset('css\visibility_report.css')}}">



<div class="card card-secondary container">
    <div class="card-header">
        <h3 class="card-title">Visibility Report</h3>
    </div>
    <form action="{{ route('getdata') }}" method="POST">
        @csrf
        @php
        $today = date('Y-m-d');
        @endphp

        <div class="card-body row">
            <div class="form-group col">
                <label for="section">Section</label>
                <select name="section" class="form-control" id="section" required>
                    <option value="motor2">Motor</option>
                    <option value="health2">Health</option>
                    <option value="term">Term</option>
                    <option value="investment">Investment</option>
                </select>
            </div>
            <div class="form-group col">
                <label for="from_date">From Date</label>
                <input type="date" name="from_date" class="form-control" id="from_date" value="{{ $startDate ?? '' }}"
                    max="{{ $today }}" required>
            </div>
            <div class="form-group col">
                <label for="end_date">End Date</label>
                <input type="date" name="end_date" class="form-control" id="end_date" value="{{ $endDate ?? '' }}"
                    max="{{ $today }}" required>
            </div>
            <div class="form-group col">
                <label for="method_type">Method Type</label>
                <select name="method_type" class="form-control" id="method_type" required>
                    <option value="quote">Quote</option>
                    <option value="ckyc">Ckyc</option>
                    <option value="proposal">Proposal</option>
                    <option value="all">All</option>
                </select>
            </div>
        </div>
        <div class="text-right">
            <button type="submit    " class="btn btn-secondary c_stage">Submit</button>
        </div>
    </form>
</div>
@if (!empty($data))
<div>
    <div class="container">
        <div class="table-container">
            <div class="table-title">Success Proposal</div>
            <table>
                <thead>
                    <tr>
                        <th>Section</th>
                        <th>Insurance Company Name</th>
                        <th>Insurance Company Success Count</th>
                        <th>Success Average Response Time</th>
                    </tr>
                </thead>
                <tbody>
                    @foreach($data->quote->success as $key => $value)
                    @if($key == "all_total")
                    @continue
                    @endif
                    <tr>
                        <td>{{$section}}</td>
                        <td>{{$key}}</td>
                        <td class="highlight">{{$value[0] ?? $value}}

                            <p>
                                <button type="button" class="btn btn-sm failurebtn" data-toggle="modal"
                                    data-target="#failureModal"  data-id="acko" 
                                    data-type="quote_failed" data-ic="{{$key}}" section = {{$section}} start_date = {{$start_date ?? ''}} end_date = {{$end_date ?? ''}}  total_record = {{$value[0] ?? $value}}>
                                    <i class="fa fa-eye view"></i> 
                                </button>
                                <button type="button" class="btn ml-1 downloadbtn" style="background:none" data-id="acko" 
                                data-type="quote_failed" data-ic="{{$key}}" section = {{$section}} start_date = {{$start_date ?? ''}} end_date = {{$end_date ?? ''}}  total_record = {{$value[0] ?? $value}} >
                                    <i class="fa fa-download" aria-hidden="true"></i>
                                </button>
                            </p>
                        </td>
                        <td class="highlight">{{$value[1] ?? ''}}</td>
                    </tr>
                    @endforeach
                    <!-- Add more rows as needed -->
                </tbody>
            </table>
        </div>
        <div class="table-container">
            <div class="table-title">Failure Proposal</div>
            <table>
                <thead>
                    <tr>
                        <th>Section</th>
                        <th>Insurance Company Name</th>
                        <th>Insurance Company Failure Count</th>
                        <th>Failure Average Response Time</th>
                    </tr>
                </thead>
                <tbody>
                    @foreach($data->quote->failure as $key => $value)
                    @if($key == "all_total")
                    @continue
                    @endif
                    <tr>
                        <td>{{$section}}</td>
                        <td>{{$key}}</td>
                        <td class="highlight">{{$value[0] ?? $value}}
                            <p>
                                <button type="button" class="btn btn-sm verticaleditbtn" data-toggle="modal"
                                    data-target="#exampleModal"  data-id="acko" 
                                    data-type="quote_failed" data-ic="{{$key}}" section = {{$section}} start_date = {{$start_date ?? ''}} end_date = {{$end_date ?? ''}}  total_record = {{$value[0] ?? $value}}>
                                    <i class="fa fa-eye view"></i> 
                                </button>

                                <button type="button" class="btn ml-1 downloadbtn" style="background:none" data-id="acko" 
                                data-type="quote_failed" data-ic="{{$key}}" section = {{$section}} start_date = {{$start_date ?? ''}} end_date = {{$end_date ?? ''}}  total_record = {{$value[0] ?? $value}} >
                                    <i class="fa fa-download" aria-hidden="true"></i>
                                </button>
                            </p>
                        </td>
                        <td class="highlight">{{$value[1] ?? ''}}</td>
                    </tr>
                    @endforeach
                </tbody>
            </table>
        </div>
    </div>
</div>




{{-- failure model --}}
<div class="modal fade" id="exampleModal" tabindex="-1" role="dialog" aria-labelledby="exampleModalLabel"
    aria-hidden="true">
    <div class="modal-dialog modal-lg" role="document">
        <div class="modal-content">
            <div class="modal-header">
                <h5 class="modal-title" id="exampleModalLabel">QUOTE FAILED</h5>
                <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                    <span aria-hidden="true">&times;</span>
                </button>
            </div>
            <div class="modal-body" style="overflow-x: auto; overflow-y: auto; max-height: 80vh;">
                {{-- <form id="vform"> --}}
                    {{-- <button type="submit" class="btn btn-primary">Download</button> --}}
                    <button type="button" class="btn ml-1 downloadbtn" style="background:none" data-id="acko" 
                    data-type="quote_failed" data-ic="{{$key}}" section = {{$section}} start_date = {{$start_date ?? ''}} end_date = {{$end_date ?? ''}}  total_record = {{$value[0] ?? $value}} >
                        <i class="fa fa-download" aria-hidden="true"></i>
                    </button>
                {{-- </form> --}}
            </div>

            <div class="card card-secondary">
                <div style="overflow-x:auto;">
                    <table id="example1" class="table table-bordered table-striped dataTable dtr-inline"
                        aria-describedby="example1_info" style="width: 100%;">
                        <thead>
                            <tr>
                                <th>SR.NO</th>
                                <th>LOGS LINK</th>
                                <th>ENQUIRY_ID</th>
                                <th>IC_NAME</th>
                                <th>VEHICLE_TYPE</th>
                                <th style="width: 200px;">MAKE</th>
                                <th style="width: 200px;">MODEL</th>
                                <th>VARIANT</th>
                                <th>VERSION_ID</th>
                                <th>FUEL_TYPE</th>
                                <th>VEHICLE_REGISTER_DATE</th>
                                <th>MANUFACTURE_YEAR</th>
                                <th>INSURER_MODELID</th>
                                <th>LEAD_ID</th>
                                <th>QUOTE_REFERENCE_NO</th>
                                <th>INSURER_QUOTE_ID</th>
                                <th>RESPONSE_TIME</th>
                                <th>PREVIOUS_POLICY_TYPE</th>
                                <th>PREVIOUS_POLICY_EXPIRY_DATE</th>
                                <th>CASE_TYPE</th>
                                <th>PLAN_NAME</th>
                                <th>POLICY_TYPE</th>
                                <th>RTO</th>
                                <th>IDV</th>
                                <th>QUOTE_RESPONSE</th>
                                <th>ACTIONABLE_AT</th>
                                <th>ERROR_TYPE</th>
                                <th>ERROR_CATEGORY</th>
                                <th>PREMIUM</th>
                                <th>DATE</th>
                                <th>TIME</th>
                                <th>REGISTRATION_NUMBER</th>
                            </tr>
                        </thead>
                        <tbody>
                            <tr>
                               

                            </tr>
                        </tbody>
                    </table>
                </div>
            </div>


        </div>
    </div>
</div>

{{-- succes model --}}
<div class="modal fade" id="failureModal" tabindex="-1" role="dialog" aria-labelledby="failureModalLabel"
    aria-hidden="true">
    <div class="modal-dialog modal-lg" role="document">
        <div class="modal-content">
            <div class="modal-header">
                <h5 class="modal-title" id="failureModalLabel">QUOTE SUCCESS</h5>
                <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                    <span aria-hidden="true">&times;</span>
                </button>
            </div>
            <div class="modal-body" style="overflow-x: auto; overflow-y: auto; max-height: 80vh;">
                <button type="button" class="btn ml-1 downloadbtn" style="background:none" data-id="acko" 
                data-type="quote_failed" data-ic="{{$key}}" section = {{$section}} start_date = {{$start_date ?? ''}} end_date = {{$end_date ?? ''}}  total_record = {{$value[0] ?? $value}} >
                    <i class="fa fa-download" aria-hidden="true"></i>
                </button>
            </div>

            <div class="card card-secondary">
                <div style="overflow-x:auto;">
                    <table id="example1" class="table table-bordered table-striped dataTable dtr-inline"
                        aria-describedby="example1_info" style="width: 100%;">
                        <thead>
                            <tr>
                                <th>SR.NO</th>
                                <th>LOGS LINK</th>
                                <th>ENQUIRY_ID</th>
                                <th>IC_NAME</th>
                                <th>VEHICLE_TYPE</th>
                                <th style="width: 200px;">MAKE</th>
                                <th style="width: 200px;">MODEL</th>
                                <th>VARIANT</th>
                                <th>VERSION_ID</th>
                                <th>FUEL_TYPE</th>
                                <th>VEHICLE_REGISTER_DATE</th>
                                <th>MANUFACTURE_YEAR</th>
                                <th>INSURER_MODELID</th>
                                <th>LEAD_ID</th>
                                <th>QUOTE_REFERENCE_NO</th>
                                <th>INSURER_QUOTE_ID</th>
                                <th>RESPONSE_TIME</th>
                                <th>PREVIOUS_POLICY_TYPE</th>
                                <th>PREVIOUS_POLICY_EXPIRY_DATE</th>
                                <th>CASE_TYPE</th>
                                <th>PLAN_NAME</th>
                                <th>POLICY_TYPE</th>
                                <th>RTO</th>
                                <th>IDV</th>
                                <th>QUOTE_RESPONSE</th>
                                <th>ACTIONABLE_AT</th>
                                <th>ERROR_TYPE</th>
                                <th>ERROR_CATEGORY</th>
                                <th>PREMIUM</th>
                                <th>DATE</th>
                                <th>TIME</th>
                                <th>REGISTRATION_NUMBER</th>
                            </tr>
                        </thead>
                        <tbody>
                            <tr>
                               

                            </tr>
                        </tbody>
                    </table>
                </div>
            </div>


        </div>
    </div>
</div>

@else
<div class="alert alert-danger" role="alert">

    <script>
        alert("No data found");
    </script>
  
        <strong>No data found!</strong>
</div>
@endif


<script src={{asset('Js/visibility_report.js')}}></script>

@endsection