@extends('layout.app', ['pageTitle' => '', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])


<style>
    .w-5 {
        display: none;
    }

    .pagination-class {
        height: 300px;
        display: flex;
        justify-content: center;
        margin-top: 20px;
    }

    .heading-container {
        /* background-color: aqua; */
        display: flex;
        align-items: center;
        justify-content: space-between;
        margin-bottom: 10px;
    }

    .createBtn {
        background-color: green;
        padding: 10px;
        color: white;
        border-radius: 10px;
    }

    .searchBtn {
        background-color: #007bff;
        color: white;
        padding: 10px;
        border-radius: 10px;
        border: none;
        margin-top: 5px;
    }
</style>

@section('content')


<div class="container">

    @if(session('success'))
    <div class="alert alert-success alert-dismissible fade show" role="alert">
        {{ session('success') }}
        <button type="button" class="btn-close" data-bs-dismiss="alert" aria-label="Close"></button>
    </div>
    @endif

    @if(session('error'))
    <div class="alert alert-danger alert-dismissible fade show" role="alert">
        {{ session('error') }}
        <button type="button" class="btn-close" data-bs-dismiss="alert" aria-label="Close"></button>
    </div>
    @endif

    <div class="heading-container">
        <h2>SMS Activity Logs</h2>
        <a href="{{ route('smsActivityLog.create') }}" class="createBtn">Create Sms</a>

    </div>

    <!--  Search Form -->
    <form method="GET" action="{{ route('smsActivityLog.index') }}" class="mb-4">
        <input type="text" name="search" class="form-control" placeholder="Search by mobile, type, status..." value="{{ request('search') }}">
        <button type="submit" class="searchBtn">Submit</button>
    </form>

    <a href="{{ route('smsActivityLog.export') }}" class="btn btn-success mb-3">
        Export to Excel
    </a>

    <table class="table table-bordered">
        <thead>
            <tr>
                <th>ID</th>
                <th>Mobile</th>
                <th>Type</th>
                <th>Status</th>
                <th>Message</th>
              {{-- <th>Sent At</th>--}}
                <th>Date And Time</th>
                <th>User ID</th>
                <th>Actions</th>
            </tr>
        </thead>
        <tbody>
            @forelse ($logs as $log)
            <tr>
                <td>{{ $log->id }}</td>
                <td>{{ $log->mobile }}</td>
                <td>{{ $log->type }}</td>
                <td>{{ $log->status }}</td>
                <td>{{ $log->message }}</td>
               {{-- <td>{{ $log->sent_at }}</td> --}}
                <td>{{$log->created_at}}</td>
                <td>{{ $log->user_id }}</td>
                <td>
                    <a href="{{ route('smsActivityLog.edit', $log->id) }}"
                        class="btn btn-sm btn-outline-info m-1" data-toggle="tooltip"
                        title="Edit ">Edit<i class="fa-solid fa-pen-to-square pl-1"></i></a>

                    <form action="{{ route('smsActivityLog.destroy', $log->id) }}" method="POST" onsubmit="return confirm('Delete this log?')">
                        @csrf
                        @method('POST')
                        <button class="btn btn-sm btn-danger">Delete</button>
                    </form>
                </td>
            </tr>
            @empty
            <tr>
                <td colspan="7">No records found.</td>
            </tr>
            @endforelse
        </tbody>
    </table>

    <!-- Pagination -->
    <div class="pagination-class">
        {{ $logs->appends(['search' => request('search')])->links() }}
    </div>

</div>
<script src="{{asset('Js/SmsActivityLog.js')}}"></script>

@endsection
