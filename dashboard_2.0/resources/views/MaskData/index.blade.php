@extends('layout.app', [
    'pageTitle' => 'Mask Data',
    'pageHeader' => 'Mask Data',
    'menu' => 'Mask Data',
    'subMenu' => 'Mask Data',
])

@section('content')
    <section class="content">
        <div class="container-fluid">
            <div class="row">
                <div class="col-12">

                    <div class="card">
                        <div class="card-header">

                            @if (session('success'))
                                <div id="flash-message" class="alert alert-success alert-dismissible fade show">
                                    {{ session('success') }}
                                    <button type="button" class="close" data-dismiss="alert">&times;</button>
                                </div>
                            @endif

                            <a class="btn btn-dark float-right" href="{{ route('MaskData.create') }}">
                                ADD <i class="fa-solid fa-plus"></i>
                            </a>
                        </div>

                        <div class="card-body">

                            <table id="example1" class="table table-bordered table-striped">
                                <thead>
                                    <tr>
                                        <th style="width:100px;">Actions</th>
                                        <th style="width:80px;">ID</th>
                                        <th>Field Name</th>
                                        <th>Status</th>
                                    </tr>
                                </thead>

                                <tbody>
                                    @foreach ($MaskData as $key => $data)
                                        <tr>
                                            <td>
                                                <div class="action-btns">

                                                    <a href="{{ route('MaskData.edit', $data->id) }}"
                                                        class="btn btn-sm btn-warning" title="Edit">
                                                        <i class="fas fa-pencil-alt"></i>
                                                    </a>

                                                    <form action="{{ route('MaskData.destroy', $data->id) }}" method="POST"
                                                        onsubmit="return confirm('Are you sure..?')">
                                                        @csrf
                                                        @method('DELETE')

                                                        <button type="submit" class="btn btn-sm btn-danger" title="Delete">
                                                            <i class="fa fa-trash"></i>
                                                        </button>
                                                    </form>

                                                </div>
                                            </td>

                                            <td>{{ $key + 1 }}</td>
                                            <td>{{ $data->field_name }}</td>
                                            <td>{{ $data->status }}</td>
                                        </tr>
                                    @endforeach
                                </tbody>

                            </table>

                        </div>
                    </div>

                </div>
            </div>
        </div>
    </section>

    {{-- ✅ Styles --}}
    <style>
        table td,
        table th {
            vertical-align: middle !important;
        }

        .action-btns {
            display: flex;
            align-items: center;
            gap: 6px;
            white-space: nowrap;
        }

        .action-btns form {
            margin: 0;
        }

        .action-btns .btn {
            padding: 4px 8px;
        }
    </style>

    {{-- ✅ Scripts --}}
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>

    <script>
        $(function() {

            $('#example1').DataTable({
                responsive: true,
                autoWidth: false,
                columnDefs: [{
                        width: "100px",
                        targets: 0
                    },
                    {
                        width: "80px",
                        targets: 1
                    }
                ]
            });

            // Auto hide flash message
            setTimeout(function() {
                $('#flash-message').alert('close');
            }, 5000);
        });
    </script>
@endsection
