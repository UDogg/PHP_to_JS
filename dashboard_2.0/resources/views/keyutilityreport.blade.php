@extends('layout.app', ['title' => 'Report Key Utility'])
<!-- Main content -->
@section('content')
    <section class="content">
        <div class="card card-secondary">
            <div class="card-header">
                <h3 class="card-title">Key utility</h3>
            </div>
            <div class="card-body">
                <form method="post" name="key_utility_frm" action="{{route('reportKeyUtility.store')}}">
                    @csrf
                    <input type="hidden" name="update_mode">
                    <div class="row">
                        <div class="col-sm-12">
                            <div class="form-group">
                                <label for="exampleInputEmail1">Name</label>
                                <input type="text" class="form-control" name="key_name" id="" value="" placeholder="Enter The Common Name Or Key Form Multiple Data ">
                            </div>
                        </div>
                        
                        <div class="col-sm-4">
                            <label for="exampleInputEmail1">Groups</label>
                            
                            <div class="form-group">
                                <select name="columns[]" id="" multiple="" data-placeholder="please select values" class="select2 select2-hidden-accessible form-control" style="width: 100%;"  tabindex="-1" aria-hidden="true">
                                    @foreach($key_utility  as $key_utility_val)
                                    <option value="">Select</option>
                                            <option value="{{$key_utility_val->id}}">{{$key_utility_val->key}}</option>
                                    @endforeach
                                </select>
                            </div>
                            
                        </div>
                       
                    </div>
                    <div class="row">
                        <div class="col-sm-2">
                            <button type="button" class="btn btn-secondary btn-sm submit_btn">submit</button>
                        </div>
                    </div>
            </div>
        </div>
    </form>

        <div class="card">
            <div class="card-header">
                <h3 class="card-title ">Key Utility List View</h3>
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
                            <form action="" method="get">
                                <div id="example1_filter" class="dataTables_filter"><input type="text" class="form-control form-control-sm" name="search" placeholder="Search" aria-controls="example1"><button class="btn btn-sm btn-secondary ml-2" type="submit">Search</button>
                            </div>
                        </form>
                    </div>
                </div>

                <div id="sortable-container" class="row mt-3">
                    <meta name="csrf-token" content="{{ csrf_token() }}">
                    <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                    @foreach($group_report_data as $gkey => $val)

                    @foreach($val as $keyUtility)
                    {{-- {{dd($keyUtility->sub)}} --}}
                    @php
                    $keyUtilityReportId = $keyUtility->key_utility_report_id;
                    $keyUtilityname = $keyUtility->sub;
                    @endphp
                    @endforeach
                    <div class="col-sm-6 draggable-item" data-id="{{ $keyUtilityReportId }}">
                        {{-- {{dd($keyUtilityReportId)}} --}}
                        <div class="card">
                            <div class="name_styling_container" style="display: flex; justify-content: space-between;border-bottom: 1px solid #ccc;">
                                <div class="heading-container">
                                    <h4 class="card-header">
                                        <b>{{ $gkey }}
                                            <i class="fa-solid fa-trash ml-3 del_icn" style="width: 10px; height: 10px" name="{{$keyUtilityname}}"></i>
                                        </b>
                                    </h4>
                                </div>

                                <div style=" margin: 10px;">
                                    <a href="{{ route('reportKeyUtility.edit', ['reportKeyUtility' => $keyUtilityname]) }}"
                                        style="padding: 6px 12px; margin: 10px; background-color: #007bff; color: white; border: none; border-radius: 4px; cursor: pointer; text-decoration: none;">
                                        Edit
                                    </a>
                                </div>

                            </div>

                            <div class="card-body">
                                <div class="row">
                                    @foreach($val as $value)

                                    <div class="col-sm-3">
                                        <p class="card-text">
                                            <button keychildid="" class="btn btn-sm btn-secondary mt-3 keychild">{{ $value->key }}</button>
                                            <img class="mt-2 del_img" src="{{ asset('Img/icons8-delete-trash-24.png') }}" alt="Delete Icon" del_id="{{$value->key_utility_report_id}}">
                                        </p>
                                    </div>
                                    @endforeach
                                </div>
                            </div>
                        </div>
                    </div>
                    @endforeach
                </div>
            </div>

        </div>
        <div class="modal fade" id="del_mdl">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h4 class="modal-title">Default Modal</h4>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">×</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <p>This will delete all the columns related to this key are you sure to proceed </p>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" class="btn btn-primary del_cnf">Save changes</button>
                    </div>
                </div>
            </div>
        </div>

            </div>

        </div>
    </section>
    <script>  var baseUrl = '{{ env("APP_URL") }}';</script>
    <script src="{{asset('Js/reportkeyutility.js')}}"></script>
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/Sortable/1.14.0/Sortable.min.js"></script>
@endsection
