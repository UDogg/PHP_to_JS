@extends('layout.app', ['activePage' => 'admin', 'titlePage' => __('Template Edit')])
@section('content')
    <!-- partial -->
    <style>
        .ck-content {
            height: 200px;
        }

        .dropbtn {
            background-color: #3498DB;
            color: white;
            padding: 16px;
            font-size: 16px;
            border: none;
            cursor: pointer;
        }

        .dropbtn:hover,
        .dropbtn:focus {
            background-color: #2980B9;
        }

        #dropdown {
            position: relative;
            display: flex;
            margin-top: 20px;
        }

        .dropdown-content {
            display: none;
            position: relative;
            background-color: #f1f1f1;
            min-width: 160px;
            overflow: auto;
            box-shadow: 0px 8px 16px 0px rgba(0, 0, 0, 0.2);
            z-index: 1;
        }

        .dropdown-content p {
            color: black;
            padding: 12px 16px;
            text-decoration: none;
            display: block;
            cursor: pointer;
        }

        .dropdown p:hover {
            background-color: #ddd;
        }

        .show {
            display: block;
        }
    </style>
    <link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/css/bootstrap.min.css"
    integrity="sha384-ggOyR0iXCbMQv3Xipma34MD+dH/1fQ784/j6cY/iJTQUOhcWr7x9JvoRxT2MZw1T" crossorigin="anonymous">
    <div class="content">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-body">
                        {{-- <h5 class="card-title">Edit Template</h5> --}}
                        @if (session('status'))
                            <div class="alert alert-{{ session('class') }}">
                                {{ session('status') }}
                            </div>
                        @endif
                        @if (session('is_configured'))
                            <div class="alert alert-danger">{{ session('is_configured') }}</div>
                        @endif
                        <form action="{{ route('template.update', $template) }}" method="POST">@csrf @method('PUT')
                            <div class="form-group row" style="display: flex; flex-direction: row; align-items: center;">
                                <label for="title" class="col-sm-2 col-form-label required">Title</label>
                                <div class="col-sm-10">
                                    <input type="text" name="title" class="form-control" id="title"
                                        placeholder="Title" value="{{ $template->title }}">
                                    @error('title')
                                        <span class="text-danger">{{ $message }}</span>
                                    @enderror
                                </div>
                            </div>
                            <div class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="communication_type" class="col-sm-2 col-form-label required">Communication
                                        Type</label>
                                    <div class="col-sm-10">
                                        <select class="form-control" id="communication_type" name="communication_type" required>
                                            <option value="sms" {{ old('communication_type', $template->communication_type) == 'sms' ? 'selected' : '' }}>sms</option>
                                            <option value="email" {{ old('communication_type', $template->communication_type) == 'email' ? 'selected' : '' }}>email</option>
                                            <option value="whatsapp" {{ old('communication_type', $template->communication_type) == 'whatsapp' ? 'selected' : '' }}>whatsapp</option>
                                        </select>
                                    </div>
                                </div>

                            <div id="dlt_id" class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="dlt_id" class="col-sm-2 col-form-label required">DLT ID</label>
                                    <div class="col-sm-10">
                                        <input type="text" name="dlt_id" class="form-control" id="dlt_id"
                                            placeholder="dlt_id" value="{{ $template->dlt_id }}">
                                        @error('dlt_id')
                                            <span class="text-danger">{{ $message }}</span>
                                        @enderror
                                    </div>
                                </div>
                                <div class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="event" class="col-sm-2 col-form-label ">Event</label>
                                    <div class="col-sm-10">
                                        <select class="form-control" id="event" name="event">
                                            @foreach ($event as $event)
                                                <option value="{{ $event }}" {{ $template->event == $event ? 'selected' : '' }}>{{ $event }}</option>
                                            @endforeach
                                        </select>
                                    </div>
                                </div>

                            <div class="form-group row" style="display: flex; flex-direction: row; align-items: center;">
                                <label for="email" class="col-sm-2 col-form-label required">Content</label>
                                <div class="col-sm-10">
                                    <textarea name="content" id="content" placeholder="Content" autocomplete="off" style="height:200px;width:100%">{{ old('content', $template->content) }}</textarea>
                                    @error('content')
                                        <span class="text-danger">{{ $message }}</span>
                                    @enderror
                                </div>
                            </div>


                            <div class="form-group row" style="display: flex; flex-direction: row; align-items: center;">
                                <label for="status" class="col-sm-2 col-form-label required">Status</label>
                                <div class="col-sm-2">
                                    <div class="form-check form-switch">
                                        <input class="form-check-input" type="checkbox" role="switch" id="status"
                                            name= "status" {{ $template->status == 'Active' ? 'checked' : '' }}>
                                    </div>
                                    @error('status')
                                        <span class="text-danger">{{ $message }}</span>
                                    @enderror
                                </div>
                            </div>
                            <button type="submit" class="btn btn-primary me-2">Submit</button>
                        </form>
                    </div>
                </div>


                <div class="modal fade" id="exampleModal" tabindex="1" aria-labelledby="exampleModalLabel"
                    aria-hidden="true">
                    <div class="modal-dialog">
                        <form action="{{ route('template.store') }}" enctype="multipart/form-data" method="post"
                            id="update-logo">@csrf
                            <div class="modal-content">
                                <div class="modal-header">
                                    <h5 class="modal-title" id="exampleModalLabel1"></h5>
                                    <button type="button" class="close" data-bs-dismiss="modal" aria-label="Close">
                                        <span aria-hidden="true">&times;</span>
                                    </button>
                                </div>
                                <div class="modal-body">
                                    <div class="form-group">
                                        <div class="form-group row"
                                            style="display: flex; flex-direction: row; align-items: center;">
                                            <label for="option_name" class="col-sm-4 col-form-label">Option Name</label>
                                            <div class="col-sm-6">
                                                <input type="text" name="option_name" class="form-control"
                                                    id="option_name" placeholder="Option Name">
                                            </div>
                                            <div class="col-sm-6" style="display: none">
                                                <input type="text" name="option_edit" class="form-control"
                                                    id="option_edit" placeholder="option_edit">
                                            </div>
                                        </div>
                                    </div>
                                </div>
                                <div class="modal-footer">
                                    <button type="button" class="btn btn-secondary"
                                        data-bs-dismiss="modal">Close</button>
                                    <button type="submit" class="btn btn-primary">Save</button>
                                </div>
                            </div>
                        </form>
                    </div>
                </div>


            </div>
        </div>
    </div>

{{-- <head>

    <link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/css/bootstrap.min.css">
    </head> --}}

    {{-- <script src={{asset('public\dist\js\ckeditor.js')}}></script>
    <script src={{asset('public\Js\template_master.js')}}></script> --}}
    <script src="https://cdn.ckeditor.com/ckeditor5/23.0.0/classic/ckeditor.js"></script>
    <script>
    function myFunction() {
        document.getElementById("myDropdown").classList.add("show");
    }
    $(document).ready(function() {
        ClassicEditor
            .create(document.querySelector('#content'))
            .then(editor => {
                const addVariableButton = document.getElementById('add_variable');

                addVariableButton.addEventListener('click', function() {
                    const viewFragment = editor.data.processor.toView('{#var}');
                    const modelFragment = editor.data.toModel(viewFragment);

                    editor.model.insertContent(modelFragment);
                });
                const addLineButton = document.getElementById('add_new_line');

                addLineButton.addEventListener('click', function() {
                    const viewFragment = editor.data.processor.toView('\\n');
                    const modelFragment = editor.data.toModel(viewFragment);

                    editor.model.insertContent(modelFragment);
                });
            })
            .then(editor => {
                const addLineButton = document.getElementById('add_new_line');

                addLineButton.addEventListener('click', function() {
                    const viewFragment = editor.data.processor.toView('\\n');
                    const modelFragment = editor.data.toModel(viewFragment);

                    editor.model.insertContent(modelFragment);
                });
            })
            .catch(error => {
                console.error(error);
            });


        $('#communication_type').change(function() {
            var communicationType = $(this).val();
            $('#email_template, #sms_template, #whatsapp_template').hide(); // Hide all templates
            if (communicationType === 'email') {
                $('#content_field').show();
                $('#dlt_id').hide();
                $('#communication_email').hide();
                ClassicEditor.create(document.querySelector('#email_content')).catch(error => console
                    .error(error));
            } else if (communicationType === 'sms') {

                $('#content_field').show();
                $('#dlt_id').show();
                $('#email_field').hide();

            } else if (communicationType === 'whatsapp') {

                 $('#content_field').show();
                $('#dlt_id').show();

            }
        });

        // Trigger change event on page load if there's a pre-selected value
        $('#communication_type').trigger('change');


        setTimeout(function() {
            $('.alert-success').hide();
        }, 1000);
    });</script>


@endsection
