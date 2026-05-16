@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
<!DOCTYPE html>
<html lang="en">

<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>CTA Master</title>
    <link rel="stylesheet" href={{ asset('public\dist\css\bootstrap_jsdelivercdn.css') }}>

    <link rel="stylesheet" href="{{url('plugins/select2/css/select2.min.css')}}">
</head>

<body>
    <div class="container mt-4">
        <h2 class="text-center">CTA Master</h2>
        <div class="card-header">
            @if (session('class'))
                <div id="flash-message" class="alert alert-{{ session('class') }} alert-dismissible fade show" role="alert">
                    {{ session('message') }}
                    <button type="button" class="close" data-dismiss="alert" aria-label="Close">
                        <span aria-hidden="true">&times;</span>
                    </button>
                </div>
            @endif
            <a id="addButton" class="btn btn-dark float-right" href="#" data-toggle="modal" data-target="#addModal">ADD <i class="fa-solid fa-plus"></i></a>
            <div id="col-md-6">
                <label for="lob-filter">Filter by LOB:</label>
                    <select id="lob-filter" class="form-control">
                        <option value="">All</option>
                        @foreach ($lobMasterData as $lob)
                            <option value="{{ $lob->lob }}">{{ $lob->lob }}</option>
                        @endforeach
                    </select>
            </div>
            <div id="error-messages" class="alert alert-danger d-none"></div>
            <!--Create Modal -->
            <div class="modal fade" id="addModal" tabindex="-1" role="dialog" aria-labelledby="addModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="addModalLabel">Add CTA</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">

                                <form method="post" name="stage_master" id="sstMasterForm">
                                @csrf
                        <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">

                                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                                <div class="form-group">
                                    <div class="row">

                                        <div class="col-md-6">
                                            <label for="lobMasterData" class = "required">Lob Master</label>
                                            <select id="lobMasterData" name="lobMasterData" class="form-control" required>
                                                <option value="" {{ old('lobMasterData') == '' ? 'selected' : '' }}>
                                                    Select Lob Master
                                                </option>
                                                @foreach ($lobMasterData as $lobMaster)
                                                    <option value="{{ $lobMaster->id }}" {{ old('lobMaster') == $lobMaster->id ? 'selected' : '' }}>
                                                        {{ $lobMaster->lob }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="stageMasterData" class="required">Stage Master</label>
                                            <select id="stageMasterData" name="stageMasterData" class="form-control" required>
                                                <option value="" {{ old('stageMasterData') == '' ? 'selected' : '' }}>
                                                    Select Stage Master
                                                </option>
                                                @foreach ($stageMasterData as $stageMaster)
                                                    <option value="{{ $stageMaster->id }}" {{ old('stageMasterData') == $stageMaster->id ? 'selected' : '' }}>
                                                        {{ $stageMaster->stage_name }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>

                                        <div class="col-md-6">
                                            <label for="ctaName" class="required">CTA Name</label>
                                            <select id="ctaName" name="ctaName" class="form-control select2">
                                                <option value="" disabled selected>Select CTA Name</option>
                                                @foreach ($ctaName as $ctaNames)
                                                    <option value="{{ $ctaNames->column_name }}">
                                                        {{ $ctaNames->column_name }}
                                                    </option>
                                                @endforeach
                                            </select>
                                        </div>



                                        <div class="col-md-6">
                                            <label for="redirection_url" >Redirection Url</label>
                                            <input type="text" class="form-control" id="redirection_url" placeholder="Enter redirection_url" name="redirection_url" value="{{ old('redirection_url') }}">
                                        </div>
                                    </div>
                                </div>
                                <div class="modal-footer">
                                    <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                                    <button type="submit" class="btn btn-dark">Submit</button>
                                </div>
                            </form>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Edit CTA Modal -->
            <div class="modal fade" id="editFieldModal" tabindex="-1" role="dialog" aria-labelledby="editCtaModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editCtaModalLabel">Edit CTA</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editCtaForm">
                                @csrf
                                <input type="hidden" name="_method" value="PUT">
                                <input type="hidden" name="apitoken" value="{{ request()->cookie('Token') }}">
                                <input type="hidden" id="cta_id" name="id">
            
                                <div class="form-group">
                                    <label for="editLobMasterData" class="required">Lob Master</label>
                                    <select id="editLobMasterData" name="lobMasterData" class="form-control" required>
                                        <option value="" disabled>Select Lob Master</option>
                                        @foreach ($lobMasterData as $lobMaster)
                                            <option value="{{ $lobMaster->id }}">{{ $lobMaster->lob }}</option>
                                        @endforeach
                                    </select>
                                </div>
            
                                <div class="form-group">
                                    <label for="editStageMasterData" class="required">Stage Master</label>
                                    <select id="editStageMasterData" name="stageMasterData" class="form-control" required>
                                        <option value="" disabled>Select Stage Master</option>
                                        @foreach ($stageMasterData as $stageMaster)
                                            <option value="{{ $stageMaster->id }}">{{ $stageMaster->stage_name }}</option>
                                        @endforeach
                                    </select>
                                </div>
            
                                <div class="form-group">
                                    <label for="editCtaName" class="required">CTA Name</label>
                                    <select id="editCtaName" name="ctaName" class="form-control" required>
                                        <option value="" disabled>Select CTA Name</option>
                                        @foreach ($ctaName as $ctaNames)
                                            <option value="{{ $ctaNames->column_name }}">{{ $ctaNames->column_name }}</option>
                                        @endforeach
                                    </select>
                                </div>
            
                                <div class="form-group">
                                    <label for="editRedirectionUrl">Redirection URL</label>
                                    <input type="text" class="form-control" id="editRedirectionUrl" name="redirection_url">
                                </div>
            
                                <div class="modal-footer">
                                    <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                                    <button type="submit" class="btn btn-dark">Save Changes</button>
                                </div>
                            </form>
                        </div>
                    </div>
                </div>
            </div>
            


        </div>


        <div class="card mt-4">
            {{-- listing for SST Master --}}
            <table id="cta-table-body" class="table">
                <thead>
                    <tr>

                        <th>LOB</th>
                        <th>Stage Name</th>
                        <th>CTA Name</th>
                        <th>Redirection URL</th>

                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>
                    @if(isset($cta) && count($cta) > 0)


                        @foreach ($cta as $ctas)
                            <tr>
                                <td>{{ $ctas->lob  }}</td>
                                <td>{{ $ctas->stage_name  }}</td>
                                <td>{{ $ctas->cta_name }}</td>
                                <td>{{ $ctas->redirection_url }}</td>

                                <td>
                                    <button class="btn btn-sm btn-primary edit-section-field"
                                        data-id="{{ $ctas->id }}"
                                        data-name="{{$ctas->lob_id }}"
                                        data-key="{{ $ctas->stage_id }}"
                                        data-value="{{ $ctas->cta_name }}"
                                        data-url="{{ $ctas->redirection_url }}"

                                        data-toggle="modal"
                                        data-target="#editFieldModal">
                                        Edit
                                    </button>
                                    <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $ctas->id }}" id="delete-sst">
                                        Delete
                                    </button>
                                </td>
                            </tr>
                        @endforeach
                    @else
                        <tr>
                            <td colspan="9" class="text-center">No CTA's data available.</td>
                        </tr>
                    @endif



                </tbody>

            </table>
        </div>
        <div class="card mt-4">
            <div class="card-header">Policy Proposal Report</div>

        </div>
        <div class="card mt-4">

            <div class="card-header d-flex justify-content-between align-items-center">
                <span>Renewals</span>
                <div class="btn-group ms-auto">
                    <button type="button" class="btn btn-primary dropdown-toggle" data-toggle="dropdown"
                        aria-haspopup="true" aria-expanded="false">
                        Select Policy Type
                    </button>
                    <div class="dropdown-menu dropdown-menu-right">
                        <a class="dropdown-item" href="#">All</a>
                        <a class="dropdown-item" href="#">Online</a>
                        <a class="dropdown-item" href="#">Offline</a>
                    </div>
                </div>
            </div>

            <div class="card-body">
                @foreach($lobMasterData as $key => $value)

                <h5>{{$value['lob_name']}}</h5>
                <div class="row mb-3">
                    <div class="col-md-6">
                        <label>Redirect to IC page</label>
                        <input type="text" class="form-control" placeholder="CTA NAME">
                    </div>
                    <div class="col-md-6">
                        <label>Redirection Link</label>
                        <input type="text" class="form-control" placeholder="Redirection Link">
                    </div>
                </div>
                <div class="row mb-3">
                    <div class="col-md-6">
                        <label>Redirect to Roll over Renewal</label>
                        <input type="text" class="form-control" placeholder="CTA NAME">
                    </div>
                    <div class="col-md-6">
                        <label>Redirection Link</label>
                        <input type="text" class="form-control" placeholder="Redirection Link">
                    </div>
                </div>
                <div class="row mb-3">
                    <div class="col-md-6">
                        <label>Renew</label>
                        <input type="text" class="form-control" placeholder="CTA NAME">
                    </div>
                    <div class="col-md-6">
                        <label>Redirection Link</label>
                        <input type="text" class="form-control" placeholder="Redirection Link">
                    </div>
                </div>
                <br><br>
                @endforeach
                <div class="text-center mt-3">
                    <button class="btn btn-primary">SAVE</button>
                </div>

            </div>
        </div>

    </div>

    <script src="{{ asset('Js/cta_master.js') }}"></script>
    <!-- Include Select2 CSS -->
<!-- Include Select2 CSS -->
<link href="https://cdn.jsdelivr.net/npm/select2@4.1.0-rc.0/dist/css/select2.min.css" rel="stylesheet" />

<!-- Include jQuery (if not already included) -->
<script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>

<!-- Include Select2 JS -->
<script src="https://cdn.jsdelivr.net/npm/select2@4.1.0-rc.0/dist/js/select2.min.js"></script>

</body>

</html>
@endsection
