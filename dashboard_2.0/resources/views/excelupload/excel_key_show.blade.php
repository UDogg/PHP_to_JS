@extends('layout.app', ['title' => 'Excel Key Show'])

    @section('content')
    <section class="content">
        <div class="container-fluid">
            <div class="card">
                {{-- <div class="card-header">
                    <h3 class="card-title"></h3>
                </div> --}}
                <!-- /.card-header -->
                <div class="card-body">
                    <table class="table table-bordered">
                        <thead>
                            <tr>
                                <th colspan="4">
                                    <label for="tableDropdown">LOB</label>
                                    <select name="lob_id" class="form-control" id="lobSelect">
                                        <option value="">Select LOB</option>
                                        @foreach($lobs as $lob)
                                            <option value="{{ $lob->id }}">{{ $lob->lob }}</option>
                                        @endforeach
                                    </select>
                                </th>
                            </tr>
                            <tr>
                                <th>Key Name</th>
                                <th>Key Sample Data</th>
                                <th>Excel Column Name</th>
                                <th>Sequence</th>
                            </tr>
                        </thead>
                        <tbody id="tableBody">
                            <tr>
                                <td></td>
                                <td></td>
                                <td></td>
                                <td></td>
                            </tr>
                        </tbody>
                    </table>
                    <br>
                    <button type="submit" id="submit" class="btn btn-primary">Submit</button>
                </div>
            </div>
        </div>
    </section>
    <meta name="csrf-token" content="{{ csrf_token() }}">
    <script>  var baseUrl = '{{ env("APP_URL") }}';</script>
    <script src="{{ asset('Js/excel_key_show.js') }}"></script>
    @endsection