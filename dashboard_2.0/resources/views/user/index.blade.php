@extends('layout.app', ['pageTitle' => 'User', 'pageHeader' => 'User', 'menu' => 'User', 'subMenu' => 'User'])
<!-- Main content -->
<style>
    .w-5 {
        display: none;
    }

    .pagination-class {
        display: flex;
        justify-content: center;
        align-items: center;
        /* padding: 10px; */
        padding-top: 20px;
    }
</style>
@section('content')
    <section class="content" style="overflow:scroll">
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
                            @if(\Illuminate\Support\Facades\Auth::user()->can('user.edit'))
                                <a class="btn btn-dark float-right" href="{{ route('user.create') }}">ADD <i
                                    class="fa-solid fa-plus"></i></a>
                            @endif
                        </div>
                       
                    </div>
                    <form action="{{ route('user.index') }}" method="GET" class="d-flex justify-content-center align-items-center gap-2 my-3" style="gap: 12px;width:100%">
                        <input type="text" name="search" value="{{ request('search') }}"
                            placeholder="Search users..."
                            class="form-control w-50 shadow-sm px-3">

                        <button type="submit" class="btn btn-primary px-4">Search</button>
                    </form>
                    <!-- /.card-header -->
                    <div class="card-body">
                        <table id="userTable" class="table table-bordered table-striped">
                            <thead>
                                <tr>
                                    <th>Actions</th>
                                    @foreach ($columns as $column)
                                    <th>{{ $column }}</th>
                                    @endforeach
                                </tr>
                            </thead>
                            <tbody>
                                @php
                                $loggedInUser = \Illuminate\Support\Facades\Auth::user();
                                @endphp
                                    @foreach ($users as $user)
                                        <tr>
                                            <td>
                                                <form id="deleteForm{{ $user->id }}" action="{{ route('user.destroy', $user->id) }}" method="post"
                                                    onsubmit="return confirm('Are you sure..?')">
                                                    @csrf
                                                    @method('DELETE')
                                                    {{-- <button type="submit" class="btn btn-sm btn-outline-danger" data-toggle="tooltip" title="Delete User"><i class="fa-solid fa-trash"></i></button> --}}
                                                    {{-- @if($loggedInUser->can('user.delete'))

                                            <button type="button" id="deleteBtn{{ $user->id }}" 
                                                class="btn btn-sm btn-outline-danger"
                                                data-toggle="modal" data-target="#deleteUserModal"
                                                onclick="setDeleteUserId('{{ $user->id }}', '{{ route('user.destroy', $user->id) }}')">
                                                <i class="fa-solid fa-trash"></i>
                                            </button>
                                            @endif --}} 

                                            @if($loggedInUser->can('user.delete'))
                                                @if($user->deleted_at)
                                                    {{-- Restore Button --}}
                                                    <button type="button"
                                                        class="btn btn-sm btn-outline-success"
                                                        onclick="restoreUser('{{ $user->id }}')"
                                                        data-toggle="tooltip" title="Restore User">
                                                        <i class="fa-solid fa-rotate-left"></i>
                                                    </button>
                                                @else
                                                    {{-- Delete Button --}}
                                                    <button type="button" id="deleteBtn{{ $user->id }}" 
                                                        class="btn btn-sm btn-outline-danger"
                                                        data-toggle="modal" data-target="#deleteUserModal"
                                                        onclick="setDeleteUserId('{{ $user->id }}', '{{ route('user.destroy', $user->id) }}')"
                                                        data-toggle="tooltip" title="Delete User">
                                                        <i class="fa-solid fa-trash"></i>
                                                    </button>
                                                @endif
                                            @endif
                                            @if(\Illuminate\Support\Facades\Auth::user()->can('user.edit'))
                                            <a href="{{ route('user.edit', $user) }}"
                                                class="btn btn-sm btn-outline-info" data-toggle="tooltip"
                                                title="Edit User"><i class="fa-solid fa-pen-to-square"></i></a>
                                            @endif
                                            <a href="{{ route('login.with.forget.password') }}"
                                                class="btn btn-sm btn-outline-info" data-toggle="tooltip"
                                                title="Forgot Password"><i class="fa-solid fa-key"></i></a>
                                            <a href="{{ route('admin.emailRequest') }}"
                                                class="btn btn-sm btn-outline-info" data-toggle="tooltip"
                                                title="Email Request"> <i class="fa-solid fa-shield-alt"></i></a>

                                            <a href="{{ route('user.editUserDoc', $user->id) }}"
                                                class="btn btn-sm btn-outline-info"
                                                title="Edit PI Data">
                                                <i class="fa-solid fa-pen-to-square"></i>
                                            </a>

                                        </form>
                                    </td>
                                    <td>{{$user->id}}</td>
                                    <td>{{ credential_decrypt($user->username) }}</td>
                                    <td>{{ credential_decrypt($user->name) }}</td>
                                    <td>{{ credential_decrypt($user->email) }}</td>
                                    <td>{{ credential_decrypt($user->mobile) }}</td>
                                    <td>{{ $user->gender }}</td>
                                    <td>{{ credential_decrypt($user->address) }}</td>
                                    <td>{{ credential_decrypt($user->pincode) }}</td>
                                    <td>{{ $user->status }}</td>
                                    <td>{{ DB::table('usertypes')->where('id', $user->usertype)->first()->name ?? '' }}</td>
                                    <td>{{ $user->role_name}}</td>
                                    <td>{{ credential_decrypt($user->reportingrolename) }}</td>
                                    <td>{{ credential_decrypt($user->adhar_no) }}</td>
                                    <td>{{ credential_decrypt($user->pan_no) }}</td>
                                    
                                </tr>
                                @endforeach
                            </tbody>
                        </table>
                        <div class="pagination-class">
                            {{ $users->appends(['search' => request('search')])->links() }}
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
        <!-- Modal for Deletion Confirmation -->
        <div class="modal fade" id="deleteUserModal"style="display: none;" aria-hidden="true">
            <div class="modal-dialog">
                <div class="modal-content">
                    <div class="modal-header">
                        <h5 class="modal-title" id="deleteUserModalLabel">Delete User</h5>
                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                            <span aria-hidden="true">&times;</span>
                        </button>
                    </div>
                    <div class="modal-body">
                        <p class="text-danger">Are you sure you want to delete this user?</p>
                    </div>
                    <div class="modal-footer justify-content-between">
                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                        <form id="deleteUserForm" method="post" action="">
                            @csrf
                            @method('DELETE')
                            <input type="hidden" name="user_id" id="user_id" value="">
                        </form>
                        <button type="button" class="btn btn-danger" onclick="confirmDeleteUser()">Delete</button>
                    </div>
                </div>
            </div>
        </div>
    </div>

    </section>

    <!-- Include jQuery and Bootstrap JavaScript (if not already included) -->
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>
    <link href="https://maxcdn.bootstrapcdn.com/bootstrap/4.5.2/css/bootstrap.min.css" rel="stylesheet">
    <script src="https://code.jquery.com/jquery-3.5.1.slim.min.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/popper.js@1.16.1/dist/umd/popper.min.js"></script>
    <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js"></script>
    {{-- <script src="https://cdn.jsdelivr.net/npm/sweetalert2@11"></script> --}}
    <script src="{{ asset('plugins/jquery/jquery.min.js') }}"></script>
    <script>
        // const Swal = require('sweetalert2')
        // Swal.fire({
        //     title: 'Error!',
        //     text: 'Do you want to continue',
        //     icon: 'error',
        //     confirmButtonText: 'Cool'
        // })
        $(document).ready(function() {
            setTimeout(function() {
                $('#flash-message').alert('close');
            }, 5000); // 5000 milliseconds = 5 seconds
        });
        $(function() {
            $('[data-toggle="tooltip"]').tooltip()
        })

        function confirmDeletion() {
            // Submit the form when OK button is clicked
            document.getElementById('deleteForm').submit();
        }

        function setDeleteUserId(userId, action) {
            document.getElementById('user_id').value = userId;
            document.getElementById('deleteUserForm').action = action;
        }

        function confirmDeleteUser() {
            document.getElementById('deleteUserForm').submit();
        }
        
        // AJAX request for deletion
            $.ajax({
            url: deleteUrl,
            type: 'DELETE',
            data: {
                id: userId,
                _token: '{{ csrf_token() }}'
            },
            success: function (response) {
                if (response.status === 200) {
                    window.location.href = "{{ route('user.index') }}";
                } else {
                    alert(response.message);
                }
            }
        });


        function restoreUser(userId) {
            if (confirm("Are you sure you want to restore this user?")) {
                $.ajax({
                    url: `/user/restore/${userId}`,
                    type: 'POST',
                    data: {
                        _token: '{{ csrf_token() }}'
                    },
                    success: function (response) {
                        if (response.status === 200) {
                            alert(response.message);
                            window.location.reload();
                        } else {
                            alert(response.message);
                        }
                    },
                    error: function (xhr) {
                        alert('Error restoring user.');
                    }
                });
            }
        }

    </script>
@endsection
