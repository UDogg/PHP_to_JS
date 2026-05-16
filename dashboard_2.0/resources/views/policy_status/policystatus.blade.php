@extends('layout.app', [
    'pageTitle
' => 'Dashboard',
    'pageHeader' => 'Dashboard',
    'menu' => 'Dashboard',
    'subMenu' => 'Home',
])
@section('content')

    <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <link rel="stylesheet" href={{ asset('public\dist\css\jquery.Datatables.css') }}>
        <script src={{ asset('public\dist\js\jquery-3.6.0.js') }}></script>
        <script src={{ asset('public\dist\js\1.11.5jquery.js') }}></script>
        <script src={{ asset('public\dist\js\datatableButton.js') }}></script>
        <script src={{ asset('public\dist\js\datatableColvis.js') }}></script>
        <link rel="stylesheet" href={{ asset('public\dist\css\datatableButtons.css') }}>
        <link rel="stylesheet" href="{{ asset('public\css\app.css') }}">
    </head>



    <section class="content">

        <div class="form-group">
            <input type="hidden" name="apitoken" value="{{request()->cookie('Token')}}">



            <div class="row p-3 pb-5 position-relative"> <!-- Added position-relative class -->
                <div class="filterdiv">
                    @php
                        $first = true; // Flag to check for the first button
                    @endphp
                    @foreach ($stagecount as $key => $filter_count)
                       <form >
                            @csrf
                            <button id="filterButton" name="filter_value"
                                class='filterButton {{ (isset($filter_value) && $filter_value == $key) || (!isset($filter_value) && $first) ? 'active' : '' }}'
                                value="{{ $key }}" type="submit">{{ $key }}{{ '(' . $filter_count . ')' }}</button>
                        </form>
                        @php
                            $first = false; // Set flag to false after the first iteration
                        @endphp
                    @endforeach
                </div>
            
                <div class="dropdown position-absolute" style="right: 20;"> <!-- Added position-absolute and right: 0 -->
                    <button onclick="myFunction()" class="dropbtn">
                        <img src="dist/img/filter.png" alt="filter Button" style="width:30px;height:25px;">
                    </button>
                    <div id="myDropdown" class="dropdown-content">
                        <input type="text" id="myInput" onkeyup="filterFunction()" placeholder="Search for names..">
                        <form action="" method="POST" class="Stagediv d-flex">
                            @csrf
                            @foreach ($stageFilter as $key => $item)
                                <div class="form-group rounded-lg">
                                    @csrf
                                    @php
                                    $today = date('Y-m-d'); // Get the current date in 'YYYY-MM-DD' format
                                @endphp
                                
                                @if ($item[0] == 'date')
                                    <div class="row">
                                        <div class="col-sm-6">
                                            <div class="form-group">
                                                <label for="policy_status">From Date:</label>
                                                <input type="date" class="form-control" name="start_date" id="" value="{{ $startDate ?? '' }}" max="{{ $today }}">
                                            </div>
                                        </div>
                                        <div class="col-sm-6">
                                            <div class="form-group">
                                                <label for="policy_status">To Date:</label>
                                                <input type="date" class="form-control" name="end_date" id="" value="{{ $endDate ?? '' }}" max="{{ $today }}">
                                            </div>
                                        </div>
                                    </div>
                                    @continue
                                @endif
                                
                                    <label>{{ $key }} </label>
                                    <select class="custom-select filterKey" id="{{ $key }}" name="{{ $key }}">
                                        @foreach ($item as $substage)
                                            @if ($substage == 'date')
                                                @continue
                                            @endif
                                            <option value="{{ $substage }}">{{ $substage }}</option>
                                        @endforeach
                                    </select>
                                </div>
                            @endforeach
            
                            <div class="col-sm-3 d-flex align-items-center mt-3">
                                <button id ="sidefilter"   class = "sidefilter" type="submit" startDate="{{ $startDate ?? '' }}"  endDate="{{ $endDate ?? '' }}" class="btn btn-info">Filter</button>
                                <button type="reset" class="btn btn-secondary ml-2">Reset</button>
                            </div>
                        </form>
                    </div>
                </div>
            </div>
            

                <div class="d-flex justify-content-between w-100">
                    <div>
                            <div class="dt-buttons btn-group flex-wrap btn_wrapper">
                                <button name="excelExport" value="excel" class="btn btn-info buttons-copy buttons-html5 excel">
                                    <span>Excel</span>
                                </button>
                            </div>
                    </div>

                    <form  class="d-flex">
                        {{-- <input type="text" name="search" placeholder="Search..." class="form-control mr-2">
                        <button type="submit" class="btn btn-info">Search</button> --}}
                        <input type="text" name="search" placeholder="Search..." class="form-control mr-2" id="searchInput">
                        <button  class="btn btn-info searchButton" id="searchButton">Search</button>
                    </form>
                </div>

                <table id="data-table" class="table table-striped dataTable col-12 display">
                    <div class="col-sm-12 col-md-6">
                        <thead>
                            <tr>
                                @foreach ($col_arr as $key => $value)
                                    <th class="sorting sorting_desc" tabindex="0" aria-controls="example1" rowspan="1"
                                        colspan="1" aria-label="Trace ID: activate to sort column ascending"
                                        aria-sort="descending">{{ !empty($value) ? $value : $key }}
                                    </th>
                                @endforeach
                                <th class="sorting" tabindex="0" aria-controls="example1" rowspan="1" colspan="1"
                                    aria-label="Customer Name: activate to sort column ascending">
                                    Quote Visibility
                                </th>
                            </tr>
                        </thead>
                        <tbody>
                            @php
                                $m_data = $data->toArray();
                                $m_data = $m_data['data'];
                                $bad_array = ['_id'];
                
                                function formatDate($date) {
                                    try {
                                        $dt = new DateTime($date);
                                        return $dt->format('d/m/y');
                                    } catch (Exception $e) {
                                        return $date;
                                    }
                                }
                            @endphp
                            @foreach ($m_data as $value)
                                <tr class="odd">
                                    @foreach ($col_arr as $d_key => $k_value)
                                        @if (!in_array($d_key, $bad_array))
                                            @php
                                                $display_value = isset($value[$d_key]) ? $value[$d_key] : '';
                                                if (strtotime($display_value)) {
                                                    $display_value = formatDate($display_value);
                                                }
                                            @endphp
                                            <td class="sorting_1 dtr-control"> {{ $display_value }} </td>
                                        @endif
                                    @endforeach
                                    <td>
                                        <a href="{{ $value['proposal_url'] ?? ($value['quote_url'] ?? '') }}">
                                            <button class="btn-info btn-sm"> VIEW </button>
                                        </a>
                                    </td>
                                </tr>
                            @endforeach
                        </tbody>
                    </div>
                </table>
                
                <div class="col-sm-12 col-md-5">
                    <div class="dataTables_info" id="example1_info" role="status" aria-live="polite">Showing 1
                        to @if ($listCounts < 10) {{$listCounts}} @else 10 @endif  of {{$paginationCount}} entries
                </div>
                </div>
                @if (isset($data[0]))
                    <div class="pagination-container mt-1">
                        <nav aria-label="Page navigation example">
                            <ul class="pagination">
                                @php
                                    $page_counts = ceil($listCounts / 10);
                                    $currentPage = $data->currentPage();
                                    $lastPage = $data->lastPage();
                                @endphp
                                <li class="page-item {{ $currentPage == 1 ? 'disabled' : '' }}">
                                    <a class="page-link" href="{{ $data->previousPageUrl() }}">Previous</a>
                                </li>
                                @if ($page_counts <= 5)
                                    @for ($i = 1; $i <= $page_counts; $i++)
                                        <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                            <a class="page-link" href="{{ $data->url($i) }}">{{ $i }}</a>
                                        </li>
                                    @endfor
                                @else
                                    @for ($i = 1; $i <= 2; $i++)
                                        <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                            <a class="page-link" href="{{ $data->url($i) }}">{{ $i }}</a>
                                        </li>
                                    @endfor
                                    @if ($currentPage > 2)
                                        <li class="page-item disabled"><span class="page-link">...</span></li>
                                    @endif
                                    @for ($i = max(3, $currentPage - 1); $i <= min($lastPage - 2, $currentPage + 1); $i++)
                                        <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                            <a class="page-link" href="{{ $data->url($i) }}">{{ $i }}</a>
                                        </li>
                                    @endfor
                                    @if ($currentPage < $lastPage - 3)
                                        <li class="page-item disabled"><span class="page-link">...</span></li>
                                    @endif
                                    @for ($i = $lastPage - 1; $i <= $lastPage; $i++)
                                        <li class="page-item {{ $currentPage == $i ? 'active' : '' }}">
                                            <a class="page-link" href="{{ $data->url($i) }}">{{ $i }}</a>
                                        </li>
                                    @endfor
                                @endif
                                <li class="page-item {{ $currentPage == $lastPage ? 'disabled' : '' }}">
                                    <a class="page-link" href="{{ $data->nextPageUrl() }}">Next</a>
                                </li>
                            </ul>
                        </nav>
                    </div>
                @endif

            </div>
        </div>

    </section>

    <script src={{ asset('Js\policystatus.js')}}></script>
@endsection
