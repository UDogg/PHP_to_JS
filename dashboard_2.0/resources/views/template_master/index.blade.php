@extends('layout.app', ['pageTitle' => 'Menu', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
<!-- Main content -->
@section('content')
    <section class="content">
        <div class="container-fluid">
            <div class="row">
                <div class="col-12">
                    <div class="card">
                        <div class="card-header">
                            @if (session('class'))
                                <div id="flash-message" class="alert alert-{{ session('class') }} alert-dismissible fade show"
                                    role="alert">
                                    {{ session('message') }}
                                    <button type="button" class="close" data-dismiss="alert" aria-label="Close">
                                        <span aria-hidden="true">&times;</span>
                                    </button>
                                </div>
                            @endif

                            <a href="{{ route('template.create') }}" class="btn btn-primary btn-sm float-end" id="addBtn">
                                <i class="fa fa-plus"></i> Add Template
                            </a>
                        </div>
                        <!-- /.card-header -->
                        <div class="card-body">
                            <table id="example1" class="table table-bordered table-striped">
                                <thead>
                                    <tr>
                                    <tr>
                                        <th scope="col">Sr. No.</th>
                                        {{-- <th scope="col">DLT ID</th> --}}
                                        <th scope="col">Title</th>
                                        <th scope="col">Type</th>
                                        <th scope="col">Event</th>
                                        <th scope="col">Status</th>
                                        <th scope="col">Created At</th>
                                        <th scope="col" class="text-right">Action</th>
                                    </tr>
                                    </tr>
                                </thead>
                                <tbody>
                                    @foreach ($templates as $key => $template)
                                        <tr>
                                            <td>{{ $key + 1 }}</td>
                                            <td>{{ $template->title }}</td>
                                            <td>{{ $template->communication_type }}</td>
                                            <td>{{ $template->event }}</td>
                                            <td>{{ $template->status }}</td>
                                            <td>{{ \Carbon\Carbon::parse($template->created_at)->format('d/m/Y') }}</td>
                                            <td>

                                                <button class="btn btn-sm btn-primary edit-template"
                                                    data-id="{{ $template->template_id }}"
                                                    data-title="{{ $template->title }}"
                                                    data-communication_type="{{ $template->communication_type }}"
                                                    data-dlt_id="{{ $template->dlt_id }}"
                                                    data-event="{{ $template->event }}"
                                                    data-content="{{ $template->content }}"
                                                    data-status="{{ $template->status }}" data-toggle="modal"
                                                    data-target="#editStatusModal">
                                                    <i class="fa fa-edit"></i>
                                                </button>


                                                <button class="btn btn-sm btn-danger delete-sst"
                                                    data-id="{{ $template->template_id }}">
                                                    <i class="fa fa-trash"></i>
                                                </button>

                                                <a href="{{ route('template.show', ['template' => $template->template_id]) }}"
                                                    class="btn btn-sm btn-outline-info"><i class="fas fa-eye"></i></a>
                                            </td>
                                        </tr>
                                    @endforeach
                                </tbody>
                            </table>
                        </div>
                                 {{-- </form> --}}


                        <!-- Edit Template Modal -->
                        <div class="modal fade" id="editStatusModal" tabindex="-1" role="dialog"
                            aria-labelledby="editStatusModalLabel" aria-hidden="true">
                            <div class="modal-dialog" role="document">
                                <div class="modal-content">
                                    <div class="modal-header">
                                        <h5 class="modal-title" id="editStatusModalLabel">Edit Template</h5>
                                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                            <span aria-hidden="true">&times;</span>
                                        </button>
                                    </div>
                                    <div class="modal-body">
                                        <form id="editStatusForm">
                                            @csrf
                                            <input type="hidden" name="id" id="edit_template_id">
                                            <div class="form-group">
                                                <label for="title" class="required">title</label>
                                                <input type="text" class="form-control" id="edit_template_title"
                                                    name="title">
                                            </div>

                                            <div class="col-sm-13">
                                                <label for="communication_type" class="required">Communication Type</label>
                                                <select class="form-control" id="edit_template_communication_type" name="communication_type" required>
                                                    <option value="sms">SMS</option>
                                                    <option value="email">Email</option>
                                                    <option value="whatsapp">WhatsApp</option>
                                                </select>
                                            </div>

                                            <div class="form-group">
                                                <label for="dlt_id">DLT Id</label>
                                                <input type="text" class="form-control" id="edit_template_dlt_id"
                                                    name="dlt_id">
                                            </div>
                                            <div class="form-group">
                                                <label for="event" class="required">event</label>
                                                <input type="text" class="form-control" id="edit_template_event"
                                                    name="event">
                                            </div>
                                            <div class="form-group" id='content_field'>
                                                <label for="content" class="required">content</label>

                                                    <textarea name="content" id="content_id" autocomplete="off" style="height:200px;width:100%"></textarea>
                                            </div>

                                            <div class="form-group">
                                                <label for="status" class="required">Status</label>
                                                <select class="form-control" id="edit_template_status" name="status">
                                                    <option value="Y">Active</option>
                                                    <option value="N">Inactive</option>
                                                </select>
                                            </div>





                                            <button type="submit" class="btn btn-primary">Save changes</button>
                                        </form>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                    <!-- /.card-body -->
                </div>
                <!-- /.card -->
            </div>
            <!-- /.col -->
        </div>
        <!-- /.row -->
        </div>
        <!-- /.container-fluid -->
    </section>

    <script src={{ asset('Js\template_master.js') }}></script>
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://cdn.ckeditor.com/ckeditor5/23.0.0/classic/ckeditor.js"></script>

@endsection
