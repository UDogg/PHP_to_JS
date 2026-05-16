@extends('layout.app', ['pageTitle' => 'MotorLobMapping', 'pageHeader' => 'MotorLobMapping','menu' => 'MotorLobMapping','subMenu' => 'MotorLobMapping'])

@section('content')
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
                        <a class="btn btn-dark float-right" href="{{ route('motorLobMapping.create') }}">ADD <i class="fa-solid fa-plus"></i></a>
                    </div>
                    <div class="card-body">
                        <table class="table table-bordered table-striped">
                            <thead>
                                <tr>
                                    <th>Actions</th>
                                    @foreach ($columns as $column)
                                        <th>{{ $column }}</th>
                                    @endforeach
                                </tr>
                            </thead>
                            <tbody>
                                @forelse ($mappings as $mapping)
                                    <tr>
                                        <td>
                                            <form action="{{ route('motorLobMapping.destroy', $mapping->id) }}" method="POST" onsubmit="return confirm('Are you sure..?')">
                                                @csrf
                                                @method('DELETE')
                                                <button type="submit" class="btn btn-sm btn-outline-danger"><i class="fa-solid fa-trash"></i></button>
                                            </form>
                                            <a href="{{ route('motorLobMapping.edit', $mapping->id) }}" class="btn btn-sm btn-outline-info">
                                                <i class="fa-solid fa-pen-to-square"></i>
                                            </a>
                                        </td>
                                        <td>{{ $mapping->lob }}</td>
                                        <td>{{ $mapping->motor_lob }}</td>
                                        <td>{{ $mapping->report_ob }}</td>
                                        <td>{{ $mapping->is_active }}</td>
                                        <td>{{ $mapping->created_at }}</td>
                                        <td>{{ $mapping->updated_at }}</td>
                                    </tr>
                                @empty
                                    <tr>
                                        <td colspan="{{ count($columns) + 1 }}">No records found.</td>
                                    </tr>
                                @endforelse
                            </tbody>
                        </table>

                        <div class="d-flex justify-content-end">
                            {{ $mappings->appends(request()->query())->links() }}
                        </div>
                    </div>
                </div>
            </div>
        </div>
    </div>
</section>
@endsection
