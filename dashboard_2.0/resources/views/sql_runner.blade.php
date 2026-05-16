@extends('layout.app', ['title' => 'Sql Runner'])
<!-- Main content -->
@section('content')
    <section class="content">
    <div class="card card-secondary">
        <div class="card-header">
            <h3 class="card-title">Sql Execution</h3>
        </div>
        <form method="post" name="sql_runner" >
            @csrf
            <div class="card-body">
                <div class="form-group">
                    <label for="exampleInputEmail1">Enter Sql</label>
                    <input type="text" class="form-control" id="exampleInputEmail1" name="query" placeholder="Enter Sql">
                </div>


                <button type="button" class="btn btn-secondary subbtn">Submit</button>
            </div>


        </form>
    </div>

        <div class="row">
            <div class="col-12">
                <div class="card">
                    <div class="card-body table-responsive p-0">
                        <table class="table table-head-fixed text-nowrap">
                            <thead>
                            <tr>
                                @php

                                $columns = empty($columns) ? [] : $columns;
                                $result = empty($result) ? [] : $result;
                                @endphp
                             @foreach($columns as $column)
                                <th>{{$column}}</th>
                             @endforeach
                            </tr>
                            </thead>
                            <tbody>
                            @foreach($result as $key => $value)
                                <tr>
                                @foreach($value as $val)

                                    <td>{{$val}}</td>
{{--                                    <td>John Doe</td>--}}
{{--                                    <td>11-7-2014</td>--}}
{{--                                    <td><span class="tag tag-success">Approved</span></td>--}}
{{--                                    <td>Bacon ipsum dolor sit amet salami venison chicken flank fatback doner.</td>--}}
                                @endforeach
                                </tr>
                            @endforeach

                            </tbody>
                        </table>
                    </div>

                </div>

            </div>
        </div>
    </section>
    <script src="{{asset('Js/SqlRunner.js')}}"></script>
@endsection
