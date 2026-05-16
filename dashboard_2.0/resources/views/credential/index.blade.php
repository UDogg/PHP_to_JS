@extends('layout.app', ['pageTitle' => 'Credential', 'pageHeader' => 'Credential', 'menu' => 'Credential', 'subMenu' => 'Credential'])
<!-- Main content -->
@section('content')
<head>
    <meta name="csrf-token" content="{{ csrf_token() }}">
    <meta name="app-url" content="{{ url('/') }}">

</head>
<section class="content">
    <div class="container-fluid">
        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-header">
                        @if (session('class'))
                            <div id="flash-message" class="alert alert-{{ session('class') }} alert-dismissible fade show" role="alert">
                                {{ session('message') }}
                                <button type="button" class="close" data-dismiss="alert" aria-label="Close">
                                    <span aria-hidden="true">&times;</span>
                                </button>
                            </div>
                        @endif

                        <div class="row">
                            <div class="col-md-4">
                                <label for="lob-filter">Filter by Config:</label>
                                <select id="lob-filter" class="form-control">
                                    <option value="">All</option>
                                    @foreach ($configData as $config)
                                        <option value="{{ $config->id }}">{{ $config->key }}</option>
                                    @endforeach
                                </select>
                            </div>
                            <div class="col-md-4">
                                <label for="search-input">Search:</label>
                                <div class="input-group">
                                    <input type="text" id="search-input" class="form-control" placeholder="Search Credential Label Or Credential Key" />
                                    <div class="input-group-append">
                                        <button id="search-btn" type="button" class="btn btn-dark">Search</button>
                                    </div>
                                </div>
                            </div>
                        </div>
                        
                            <a class="btn btn-dark float-right" href="{{ route('credential.create') }}">ADD <i class="fa-solid fa-plus"></i></a>


                    <!-- /.card-header -->
                    <div class="card-body">
                        <table  class="table table-bordered table-striped" id="tableList">
                            <thead>
                                <tr>
                                    <th>Actions</th>
                                    @foreach ($columns as $column)
                                        <th>{{ $column }}</th>
                                    @endforeach
                                </tr>
                            </thead>
                            <tbody id="example1">
                                @foreach ($credential as $credential)
                                    <tr>
                                        <td>
                                            <a href="{{ route('credential.edit', $credential) }}" class="btn btn-sm btn-outline-info"><i class="fa-solid fa-pen-to-square"></i></a>
                                            <form class="mt-2" action="{{ route('credential.destroy', $credential) }}" method="post" onsubmit="return confirm('Are you sure..?')">
                                            @csrf
                                            @method('DELETE')
                                            <button type="submit" class="btn btn-sm btn-outline-danger"><i class="fa-solid fa-trash"></i></button>
                                            </form>
                                        </td>
                                        <td>{{ $credential->credential_label }}</td>
                                        <td>{{ $credential->credential_key }}</td>
                                        <td>{{ $credential->credential_value }}</td>
                                        <td>{{ $credential->enviroment }}</td>
                                        <td>{{ $credential->created_at }}</td>
                                        <td>{{ $credential->updated_at }}</td>
                                    </tr>
                                @endforeach
                            </tbody>
                        </table>
                        <div class="row">
                            <div class="col-sm-12 col-md-5">
                                <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">
                                    Showing {{ ($current_page - 1) * 10 + 1 }} to {{ min($current_page * 10, $credential_count) }} of {{ $credential_count }} entries
                                </div>
                            </div>
                            <div class="col-sm-12 col-md-7">
                                <div class="dataTables_paginate paging_simple_numbers" id="example1_paginate">
                                    <ul class="pagination">
                                        <!-- Home Button -->
                                        <li class="paginate_button page-item {{ $current_page == 1 ? 'disabled' : '' }}">
                                            <a href="{{ url()->current() }}?page=1" aria-controls="example1" class="page-link">Home</a>
                                        </li>

                                        <!-- Previous Button -->
                                        <li class="paginate_button page-item {{ $current_page == 1 ? 'disabled' : '' }}">
                                            <a href="{{ url()->current() }}?page={{ $current_page - 1 }}" aria-controls="example1" class="page-link">Previous</a>
                                        </li>

                                        <!-- Pagination Links -->
                                        @if($current_page > 3)
                                            <li class="paginate_button page-item disabled">
                                                <a href="#" class="page-link">...</a>
                                            </li>
                                        @endif

                                        @for($i = 1; $i <= $page_nos; $i++)
                                            <li class="paginate_button page-item {{ $current_page == $i ? 'active' : '' }}">
                                                <a href="{{ url()->current() }}?page={{ $i }}" class="page-link">{{ $i }}</a>
                                            </li>
                                        @endfor

                                        <!-- Next Button -->
                                        <li class="paginate_button page-item {{ $current_page == $page_nos ? 'disabled' : '' }}">
                                            <a href="{{ url()->current() }}?page={{ $current_page + 1 }}" class="page-link">Next</a>
                                        </li>

                                        <!-- End Button -->
                                        <li class="paginate_button page-item {{ $current_page == $page_nos ? 'disabled' : '' }}">
                                            <a href="{{ url()->current() }}?page={{ $page_nos }}" class="page-link">End</a>
                                        </li>
                                    </ul>
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
    <script src="{{ asset('Js/credential.js') }}"></script>

<script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
</section>

<script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>


@endsection
