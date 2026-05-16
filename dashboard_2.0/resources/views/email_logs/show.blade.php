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


    <div class="heading-container">
        <h2>Email Activity Logs</h2>
    </div>


    <table class="table table-bordered">
        <thead>
            <tr>
                <th>ID</th>
                <th>Email</th>
                <th>Subject</th>
                <th>Body</th>
                <th>Status</th>
                <th>Date And Time</th>
            </tr>
        </thead>
        <tbody>
            @foreach ($logs as $log)
            <tr>
                <td>{{$log->email_id}}</td>
                <td>{{ $log->email }}</td>
                <td>{{ $log->subject }}</td>
                <td>{{ $log->body }}</td>
                <td>{{ $log->status }}</td>
                <td>{{$log->sent_at}}</td>
            </tr>
            @endforeach
        </tbody>
    </table>

    <!-- Pagination -->
    <div class="pagination-class">
        {{ $logs->appends(['search' => request('search')])->links() }}
    </div>

</div>
<script src="{{asset('Js/SmsActivityLog.js')}}"></script>

@endsection
