@extends('layout.app', ['activePage' => 'admin', 'titlePage' => __('Template Add')])
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
                        <h2> Add Template</h2><br>
                        @if (session('status'))
                            <div id="success-message" class="alert alert-{{ session('class') }}">
                                {{ session('status') }}
                            </div>
                        @endif
                        <div>
                            @if (session('is_configured'))
                                <div class="alert alert-danger">{{ session('is_configured') }}</div>
                            @endif

                            <form id="sstMasterForm" method="POST">@csrf
                                <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                                <div class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="title" class="col-sm-2 col-form-label required">Title</label>
                                    <div class="col-sm-10">
                                        <input type="text" name="title" class="form-control" id="title"
                                            placeholder="Title" value="{{ old('title') }}">
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
                                        <select class="form-control" id="communication_type" name="communication_type"
                                            required>
                                            <option value="sms">SMS</option>
                                            <option value="email">Email</option>
                                            <option value="whatsapp">WhatsApp</option>
                                        </select>
                                    </div>
                                </div>

                                <div id="dlt_id" class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="dlt_id" class="col-sm-2 col-form-label required">DLT ID</label>
                                    <div class="col-sm-10">
                                        <input type="text" name="dlt_id" class="form-control" id="dlt_id"
                                            placeholder="dlt_id" value="{{ old('dlt_id') }}">
                                        @error('dlt_id')
                                            <span class="text-danger">{{ $message }}</span>
                                        @enderror
                                    </div>
                                </div>


                                <div class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="event" class="col-sm-2 col-form-label">Event</label>
                                    <div class="col-sm-10">
                                        <select class="form-control" id="event" name="event">
                                            @foreach ($event as $event)
                                                <option value="{{ $event }}">{{ $event }}</option>
                                            @endforeach
                                        </select>
                                    </div>
                                </div>
                                <div class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;" id='content_field'>
                                    <label for="content" class="col-sm-2 col-form-label required">Content</label>
                                    <div class="col-sm-10">
                                        <textarea name="content" id="content_id" placeholder="Content" autocomplete="off" style="height:200px;width:100%">{{ old('content') }}</textarea>
                                        @error('content')
                                            <span class="text-danger">{{ $message }}</span>
                                        @enderror
                                    </div>
                                </div>


                                <div class="form-group row"
                                    style="display: flex; flex-direction: row; align-items: center;">
                                    <label for="status" class="col-sm-2 col-form-label required">Status</label>
                                    <div class="col-sm-2">
                                        <div class="form-check form-switch">
                                            <input class="form-check-input" type="checkbox" role="switch"
                                                id="status" name="status" value="on"
                                                {{ old('status') == 'off' ? '' : 'checked' }}>
                                        </div>

                                        @error('status')
                                            <span class="text-danger">{{ $message }}</span>
                                        @enderror
                                    </div>
                                </div>


                                <button type="submit" class="btn btn-primary me-2" id="submitBtn">Submit</button>
                            </form>
                        </div>
                    </div>
                </div>

            </div>
        </div>
    </div>

    <script src={{asset('Js\template_master.js')}}></script>
    <script src="https://cdn.ckeditor.com/ckeditor5/23.0.0/classic/ckeditor.js"></script>

@endsection
