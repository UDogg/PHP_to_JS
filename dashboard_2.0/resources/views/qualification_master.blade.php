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
                <h3 class="card-title">Qualification Master</h3>
            </div>
            <form method="post" name="stage_master" id="sstMasterForm">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">

                    <div class="row">

                        <div class="col-md-6">
                            <div class="form-group">
                                <label for=""> Qualification Name</label>
                                <input type="text" maxlength="50" name="qualification_name" class="form-control"
                                    id="qualification_name" placeholder="Enter Qualification Name">

                            </div>
                        </div>
                    </div>


                    <button type="submit" class="btn btn-secondary addBtn" id="submitBtnSst">Submit</button>
                </div>
            </form>
            {{-- listing for Tag Master --}}
            <table class="table">
                <thead>
                    <tr>

                        <th>Qualification Name</th>


                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>

                    @if(isset($qualification) && count($qualification) > 0)
                        @foreach ($qualification as $qualifications)
                            <tr>
                                <td>{{ $qualifications->qualification_name }}</td>


                                <td>
                                    <button class="btn btn-sm btn-primary edit-section-field"
                                        data-id="{{ $qualifications->qualification_master_id }}"
                                        data-name="{{  $qualifications->qualification_name }}"


                                        data-toggle="modal"
                                        data-target="#editFieldModal">
                                        Edit
                                    </button>
                                    <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $qualifications->qualification_master_id }}">
                                        Delete
                                    </button>
                                </td>
                            </tr>
                        @endforeach
                    @else
                        <tr>
                            <td colspan="9" class="text-center">No Tag data available.</td>
                        </tr>
                    @endif



                </tbody>
            </table>

            <!-- Edit Tag Modal -->
            <div class="modal fade" id="editfieldModal" tabindex="-1" role="dialog"
                aria-labelledby="editStatusModalLabel" aria-hidden="true">
                <div class="modal-dialog" role="document">
                    <div class="modal-content">
                        <div class="modal-header">
                            <h5 class="modal-title" id="editStatusModalLabel">Edit Qualification Name</h5>
                            <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                <span aria-hidden="true">&times;</span>
                            </button>
                        </div>
                        <div class="modal-body">
                            <form id="editfieldForm">
                                @csrf
                                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                                <input type="hidden" id="field_master_id">
                                <div class="form-group">
                                    <label for="qualification_name">Qualification Name</label>
                                    <input type="text" class="form-control" id="field_master_lob" name="qualification_name">
                                </div>


                                <button type="submit" class="btn btn-primary ">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>


        </div>




    </section>

    <script src="{{ asset('Js/qualification_master.js') }}"></script>

    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
