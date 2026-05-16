@extends('layout.app', ['title' => 'Report Key Utility'])
<!-- Main content -->

@section('content')
<section class="content">
    <div class="card card-secondary">
        <div class="card-header">
            <h3 class="card-title">Key utility</h3>
        </div>
        <div class="card-body">
            <form method="POST" action="{{ route('reportKeyUtility.update', $common_name) }}">
                @csrf
                @method('PUT')

                <div class="row">
                    <div class="col-sm-12">
                        <div class="form-group">
                            <label for="exampleInputEmail1">Name</label>
                            <input type="text" class="form-control" name="key_name" id="" value="{{ $common_name }}" placeholder="Enter The Common Name Or Key Form Multiple Data " readonly>
                        </div>
                    </div>

                    <div class="col-sm-4">
                        <label for="exampleInputEmail1">Groups</label>
                        <div class="form-group">
                            <select name="columns[]" multiple class="select2 form-control">
                                @foreach($key_utility as $key_utility_val)

                                <option value="{{ $key_utility_val->id }}"
                                    {{ in_array($key_utility_val->id, $exsiting_column_id) ? 'selected' : '' }}>
                                    {{ $key_utility_val->key }}
                                </option>
                                @endforeach
                            </select>
                        </div>




                    </div>

                </div>
                <div class="row">
                    <div class="col-sm-2">
                        <button type="submit" class="btn btn-secondary btn-sm">Submit</button>
                    </div>
                </div>
        </div>

        <a href="{{ route('reportKeyUtility.index') }}" class="btn btn-secondary btn-sm">
            ← Back
        </a>
    </div>




    </form>

</section>
<script>
    var baseUrl = '{{ env("APP_URL") }}';
</script>
<script src="{{asset('Js/reportkeyutility.js')}}"></script>
<script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/Sortable/1.14.0/Sortable.min.js"></script>
@endsection





