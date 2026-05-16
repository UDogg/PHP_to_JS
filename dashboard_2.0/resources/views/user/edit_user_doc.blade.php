@extends('layout.app', [
    'pageTitle' => 'Edit Aadhaar / PAN',
    'pageHeader' => 'Edit Aadhaar / PAN',
    'menu' => 'User',
    'subMenu' => 'User',
])

@section('content')
    <div class="container">
        <div class="card">
            <div class="card-header">
                <a href="{{ route('user.index') }}" class="btn btn-dark">
                    <i class="fa-solid fa-arrow-left"></i>
                </a>
            </div>

            <div class="card-body">
                <form action="{{ route('user.updateUserDoc', $user->id) }}" method="POST">
                    @csrf

                    <div class="row">
                        <div class="col-md-6">
                            <label class="required">Aadhaar No</label>
                            <input type="text" name="adhar_no" class="form-control"
                                value="{{ old('adhar_no', $user->adhar_no) }}" >
                        </div>

                        <div class="col-md-6">
                            <label class="required">PAN No</label>
                            <input type="text" name="pan_no" class="form-control"
                                value="{{ old('pan_no', $user->pan_no) }}" >
                        </div>
                    </div>

                    <div class="col-md-6">
                        <label for="status" class = "required">Status</label>
                        <div class="ml-2">
                            <div class="form-check form-check-inline">
                                <input class="form-check-input" type="radio" name="status" id="active" value="Y" {{ old('status', $user->status) == 'Y' ? 'checked' : '' }}>
                                <label class="form-check-label" for="active">Active</label>
                            </div>
                            <div class="form-check form-check-inline">
                                <input class="form-check-input" type="radio" name="status" id="inactive" value="N" {{ old('status', $user->status) == 'N' ? 'checked' : '' }}>
                                <label class="form-check-label" for="inactive">Inactive</label>
                            </div>
                        </div>
                    </div>
                    <div class="mt-3">
                        <button class="btn btn-dark" type="submit">Update</button>
                    </div>
                </form>
            </div>
        </div>
    </div>
@endsection
