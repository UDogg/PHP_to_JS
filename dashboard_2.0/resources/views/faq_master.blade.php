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
                <h3 class="card-title">FAQ's</h3>
            </div>
            <form method="post" name="stage_master" id="sstMasterForm">
                @csrf
                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                <div class="card-body">
                    <div class="row">

                        <div class="col">
                            <div class="form-group">
                                <label for="tag">Select Tag Name</label>
                                <select name="tag" class="form-control" id="tag">
                                    <option value="">Select Tag</option>
                                    @foreach ($tag_name as $tag)
                                        <option value="{{ $tag->tag_id }}">{{ $tag->tag_name }}</option>
                                    @endforeach
                                </select>
                            </div>
                        </div>
                    </div>
                    <div class="row">
                        <div class="col">
                            <div class="form-group">
                                <label for="">Add Question</label>

                                <textarea id="question" name= "question" class="form-control" style="height: 100px" placeholder="Enter Question"></textarea>

                            </div>
                        </div>
                    </div>


                    <div class="row">

                        <div class="col">
                            <div class="form-group">
                                <label for="">Add Answer</label>

                                <textarea id="answer" name= "answer" class="form-control" style="height: 100px" placeholder="Enter Answer"></textarea>

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

                        <th>Tag Name</th>
                        <th>Questions</th>
                        <th>Answers</th>

                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>

                    @if(isset($faq) && count($faq) > 0)
                        @foreach ($faq as $faqs)
                            <tr>
                                <td>{{ $faqs->tag_name }}</td>
                                <td>{{ $faqs->question }}</td>
                                <td>{{ $faqs->answer }}</td>

                                <td>
                                    <button class="btn btn-sm btn-primary edit-section-field"
                                        data-id="{{ $faqs->faq_id }}"
                                        data-name="{{  $faqs->tag }}"
                                        data-key="{{ $faqs->question }}"
                                        data-value="{{ $faqs->answer }}"

                                        data-toggle="modal"
                                        data-target="#editFieldModal">
                                        Edit
                                    </button>
                                    <button class="btn btn-sm btn-danger delete-sst" data-id="{{ $faqs->faq_id }}">
                                        Delete
                                    </button>
                                </td>
                            </tr>
                        @endforeach
                    @else
                        <tr>
                            <td colspan="9" class="text-center">No FAQ's data available.</td>
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
                            <h5 class="modal-title" id="editStatusModalLabel">Edit FAQ</h5>
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
                                    <label for="tag">Tag Name</label>
                                    <select name="tag" class="form-control" id="field_master_lob">
                                        <option value="">Select Tag</option>
                                        @foreach ($tag_name as $tag)
                                            <option value="{{ $tag->tag_id }}">{{ $tag->tag_name }}</option>
                                        @endforeach
                                    </select>
                                </div>

                                <div class="form-group">
                                    <label for="question">Question</label>
                                    <textarea class="form-control" id="field_master_sst" name="question"></textarea>
                                </div>

                                <div class="form-group">
                                    <label for="answer">Answer</label>
                                    <textarea class="form-control" id="field_master_section" name="answer"></textarea>
                                </div>


                                <button type="submit" class="btn btn-primary ">Save changes</button>
                            </form>
                        </div>
                    </div>
                </div>
            </div>


        </div>




    </section>

    <script src="{{ asset('Js/faq_master.js') }}"></script>

    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
@endsection
