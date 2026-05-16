@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
    <section class="content">

<div class="card card-secondary">
    <div class="card-header">

        <h3 class="card-title">Column visibility</h3>
    </div>
    <form method="post" >
        @csrf
        <div class="card-body">
            <div class="col-sm-3">
                <div class="form-group">
                    <button type="button" class="btn btn-primary" data-bs-toggle="modal" data-bs-target="#addNameModal">
                        ADD
                    </button>
                </div>
            </div>
            <div class="row mb-3">
                <div class="col-sm-6">
                    <div class="form-group">
                        <select name="lob_sel[]" id="lob_sel" class="form-control select2" multiple>

                            @foreach ($lobs as $l)
                            <option value="{{ $l->id }}"
                                        @if (in_array($l->id, (array) $selLob)) selected @endif>
                                        {{ $l->lob }}
                                        </option>
                            @endforeach
                        </select>
                    </div>
                </div>
                <div class="col-sm-6">
                    <div class="form-group">
                        <select name="sel_stage[]" id="sel_stage" class="form-control select2" multiple>
                            @foreach ($Mstages as $mstg)
                                <option value="{{ $mstg->id }}"
                                            @if (in_array($mstg->id, (array) $selStage)) selected @endif>
                                            {{ $mstg->stage_name }}
                                        </option>
                                    @endforeach
                                </select>
                            </div>
                        </div>
                        <!-- Search Column -->
                        <div class="col-sm-6">
                            <div class="form-group">
                                <input type="text" class="form-control" placeholder="Search Columns here"
                                    name="search_col">
                            </div>
                        </div>
                    </div>

                    <div class="row">
                @php
                $not_show_column_array = ['_id', 'created_at', 'updated_at'];
                @endphp
                        @if (empty($newData))
                            <div class="col-sm-6">
                                <div class="form-group">
                                    <div class="text-info">No Data is Available, Please Check With Developers</div>
                                </div>
                            </div>
                        @endif

                @foreach ($newData ?? [] as $column)
                @php
                    $colName = is_array($column) ? $column['column_name'] : $column->column_name;
                    $colAlias = is_array($column) ? $column['alias'] : $column->alias;
                    $colId = is_array($column) ? $column['id'] : $column->id;
                    $isVisible = is_array($column) ? $column['is_visible'] : $column->is_visible;
                    $isDefault = is_array($column) ? $column['is_default'] : $column->is_default;
                    $colLob = is_array($column) ? $column['lob'] : $column->lob;
                    $colStage = is_array($column) ? $column['stage'] : $column->stage;
                @endphp

                            @if (!in_array($colName, $not_show_column_array))
                                <div class="col-sm-6 mb-3">
                                    <div class="form-group">
                                        <div class="row align-items-center">
                                            <!-- Default icon toggle -->
                                            <div class="is_def"
                                                style="height:20px; width:20px; cursor:pointer; display:flex; align-items:center; justify-content:center; border:1px solid #000; background-color:{{ $isDefault == 'Y' ? 'black' : 'white' }}; margin-right:4px;"
                                                is_default="{{ empty($isDefault) ? 'N' : $isDefault }}"
                                                ed_id="{{ $colId }}" column_name="{{ $colName }}">
                                            </div>

                                            <!-- Column checkbox and label -->
                                            <div class="custom-control custom-switch">
                                                <input type="checkbox" class="custom-control-input col-checkbox"
                                                    name="col_names[]" value="{{ $colId }}"
                                                    id="chk_{{ $colId }}"
                                                    @if ($isVisible == 'Y') checked @endif>
                                                <label class="custom-control-label colnms" for="chk_{{ $colId }}"
                                                    style="margin-right:2px;">
                                                    {{ !empty($colAlias) ? $colAlias . ' (' . $colName . ')' : $colName }}
                                                    @if ($isDefault == 'Y')
                                                        <small class="text-muted"> - LOB: {{ $colLob }}, Stage:
                                                            {{ $colStage }}</small>
                                                    @endif
                                                </label>
                                            </div>

                                            <!-- Alias edit icon with reduced spacing -->
                                            <div class="fas icn alias_ed" ed_val="{{ $colName }}"
                                                ed_id="{{ $colId }}" new_val="{{ $colAlias }}"
                                                order_val="{{ is_array($column) ? $column['order_by'] : $column->order_by }}"
                                                style="height:18px; width:18px; cursor:pointer; margin-left:4px;">
                                                <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512">
                                                    <path
                                                        d="M441 58.9L453.1 71c9.4 9.4 9.4 24.6 0 33.9L424 134.1 377.9 88 407 58.9c9.4-9.4 24.6-9.4 33.9 0zM209.8 256.2L344 121.9 390.1 168 255.8 302.2c-2.9 2.9-6.5 5-10.4 6.1l-58.5 16.7 16.7-58.5c1.1-3.9 3.2-7.5 6.1-10.4zM373.1 25L175.8 222.2c-8.7 8.7-15 19.4-18.3 31.1l-28.6 100c-2.4 8.4-.1 17.4 6.1 23.6s15.2 8.5 23.6 6.1l100-28.6c11.8-3.4 22.5-9.7 31.1-18.3L487 138.9c28.1-28.1 28.1-73.7 0-101.8L474.9 25C446.8-3.1 401.2-3.1 373.1 25z" />
                                                </svg>
                                            </div>
                                        </div>
                                    </div>
                                </div>
                            @endif
                        @endforeach

                        <!-- Modal for alias edit -->
                        <div class="modal fade" id="modal-default">
                            <div class="modal-dialog">
                                <div class="modal-content">
                                    <div class="modal-header">
                                        <h4 class="modal-title">Edit Alias</h4>
                                        <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                            <span aria-hidden="true">×</span>
                                        </button>
                                    </div>
                                    <div class="modal-body">
                                        <form method="post" name="up_alias">
                                            @csrf
                                            <input type="text" class="form-control" id="alias_name"
                                                placeholder="Enter alias name">
                                            <input type="hidden" id="ed_id" value="">
                                        </form>
                                    </div>
                                    <div class="modal-body">
                                        <form method="post" name="order_by">
                                            @csrf
                                            <input type="text" class="form-control" id="order_by_input" placeholder="Enter Order">
                                            <input type="hidden" id="order_by_hidden" value="">
                                        </form>
                                    </div>
                                    <div class="modal-footer justify-content-between">
                                        <button type="button" class="btn btn-default" data-dismiss="modal">Close</button>
                                        <button type="button" class="btn btn-primary sb_clmn_up">Save changes</button>
                                    </div>
                                </div>
                            </div>
                        </div>
                        <!-- End Modal -->
                    </div>
                </div>
            </form>
        </div>

       <!-- Modal -->
    <div class="modal fade" id="addNameModal" tabindex="-1" aria-labelledby="addNameModalLabel" aria-hidden="true">
        <div class="modal-dialog">
        <div class="modal-content">
            
            <div class="modal-header">
            <h5 class="modal-title" id="addNameModalLabel">Add Column</h5>
            <button type="button" class="btn-close" data-bs-dismiss="modal" aria-label="Close"></button>
            </div>
            
            <div class="modal-body">
            <form method="POST" action="{{ route('add_column') }}">
                @csrf
                <div class="mb-3">
                <label for="ColumnName" class="form-label">Column Name</label>
                <input type="text" class="form-control" name="ColumnName" id="ColumnName" placeholder="Enter Column Name" required>
                </div>
                <div class="mb-3">
                    <label for="ColumnNameAlias" class="form-label">Alias</label>
                    <input type="text" class="form-control" name="ColumnNameAlias" id="ColumnNameAlias" placeholder="Enter Alias">
                    </div>
                <div class="mb-3">
                    <label for="selectlob" class="form-label">LOB</label>
                    <select name="selectlob[]" id="selectlob" class="form-control select2" multiple>
                        @foreach ($lobs as $lob)
                        <option value="{{ $lob->id }}"
                            @if (!empty($selLob) && in_array($lob->id, (array) $selLob)) selected @endif>
                            {{ $lob->lob }}
                        </option>
                        @endforeach
                    </select>
                </div>
                <div class="mb-3">
                    <label for="selectStage" class="form-label">STAGES</label>
                    <select name="selectStage[]" id="selectStage" class="form-control select2" multiple>
                        @foreach ($Mstages as $stage)
                            <option value="{{ $stage->id }}"
                                @if (in_array($stage->id, (array) $selStage)) selected @endif>
                                {{ $stage->stage_name }}
                            </option>
                        @endforeach
                    </select>
                </div>
                <div class="mb-3">
                    <label for="isDefault" class="form-label">Is_default</label>
                    <select name="isDefault" id="isDefault" class="form-control">
                        <option value="" disable>--Select--</option>
                        <option value="Y">YES</option>
                        <option value="N">NO</option>
                    </select>
                </div>
                <div class="mb-3">
                    <label for="isVisible" class="form-label">Is_visible</label>
                    <select name="isVisible" id="isVisible" class="form-control">
                        <option value="" disable>--Select--</option>
                        <option value="Y">YES</option>
                        <option value="N">NO</option>
                    </select>
                </div>
    
                <!-- Submit Button -->
                <button type="submit" id="addColumns" class="btn btn-success">Save</button>
            </form>
            </div>
    
        </div>
        </div>
    </div>
  
    </section>
    <!-- Include Select2 -->
    <!-- Include Select2 CSS and JS -->
    <!-- Bootstrap CSS -->
    <script src="https://cdn.jsdelivr.net/npm/bootstrap@5.3.0/dist/js/bootstrap.bundle.min.js"></script>

    <link href="https://cdn.jsdelivr.net/npm/select2@4.0.13/dist/css/select2.min.css" rel="stylesheet" />
    <script src="https://cdn.jsdelivr.net/npm/select2@4.0.13/dist/js/select2.min.js"></script>
    <script src="{{asset('Js/policystatus_column_config.js')}}"></script>
@endsection
