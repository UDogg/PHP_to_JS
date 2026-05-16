@extends('layout.app', ['pageTitle' => 'User', 'pageHeader' => 'User', 'menu' => 'User', 'subMenu' => 'User'])
@section('content')
<div class="container">
    <div class="row">
        <div class="col-12">
            <div class="card">
                <div class="card-header">
                    @if ($errors->any())
                        <div class="alert alert-danger">
                            <ul class="list">
                                @foreach ($errors->all() as $error)
                                    <li>{{ $error }}</li>
                                @endforeach
                            </ul>
                        </div>
                    @endif
                    <a  href="{{ route('user.index') }}" class="btn btn-dark"><i class="fa-solid fa-arrow-left"></i></a>
                </div>
                <!-- /.card-header -->
                <div class="card-body">
                    <form action="{{ route('user.update',$user) }}" method="POST" id="edit_form">
                        @csrf @method('PUT')
                        <div class="card-body">
                            <input type="hidden" value="{{request()->cookie('Token')}}" name="apitoken">
                            <input type="hidden" name="id" value="{{ $user->id }}">

                            <div class="form-group">
                                @if(!empty(session('message')))
                                    <div class="invalid-feedback">{{session('message')}}</div>
                                @else

                                @endif
                                <div class="row">

                                    <div class="col-md-6">
                                        <label for="username" class = "required">User Name</label>
                                        <input type="text" class="form-control" id="username"
                                            placeholder="Enter User Name" name="username" value="{{ $user->username }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="name" class = "required">Name</label>
                                        <input type="name" class="form-control" id="name"
                                            placeholder="Enter Name" name="name" value="{{ $user->name }}" required>
                                    </div>
                                </div>
                            </div>
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="email" class = "required">Email</label>
                                        <input type="text" class="form-control" id="email"
                                            placeholder="Enter Email" name="email" value="{{ $user->email }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="mobile" class = "required">Mobile</label>
                                        <input type="mobile" class="form-control" id="mobile"
                                            placeholder="Enter Mobile Number" name="mobile" value="{{ $user->mobile }}" required>
                                    </div>
                                </div>
                            </div>
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label for="address" class = "required">Address</label>
                                        <input type="text" class="form-control" id="address"
                                            placeholder="Enter Address" name="address" value="{{ $user->address }}" required>
                                    </div>
                                    <div class="col-md-6">
                                        <label for="pincode" class = "required">Pincode</label>
                                        <input type="pincode" class="form-control" id="pincode"
                                            placeholder="Enter Mobile Number" name="pincode" value="{{ $user->pincode }}" required>
                                    </div>
                                </div>
                            <div class="form-group">
                                <div class="row">
                                    <div class="col-md-6">
                                        <label class="required">Gender</label><br>
                                        <div class="form-check form-check-inline">
                                            <input class="form-check-input" type="radio" name="gender" id="male" value="M" @if(isset($user->gender) && $user->gender == 'M')  checked @endif >
                                            <label for="male" class="form-check-label">Male</label>
                                        </div>
                                        <div class="form-check form-check-inline">
                                            <input class="form-check-input" type="radio" name="gender" id="female" value="F" @if(isset($user->gender) && $user->gender == 'F')  checked @endif >
                                            <label for="female" class="form-check-label">Female</label>
                                        </div>
                                    </div>
                                    <div class="col-md-6">
                                        <label class="required">Status</label><br>
                                        <div class="form-check form-check-inline">
                                            <input class="form-check-input" type="radio" name="status" id="active" value="Y" @if(isset($user->status) && $user->status == 'Y')  checked @endif >
                                            <label for="active" class="form-check-label">Active</label>
                                        </div>
                                        <div class="form-check form-check-inline">
                                            <input class="form-check-input" type="radio" name="status" id="inactive" value="N" @if(isset($user->status) && $user->status == 'N')  checked @endif >
                                            <label for="inactive" class="form-check-label">In Active</label>
                                        </div>
                                            <div class="col-md-6">
                                                <label class="required">User Types</label><br>
                                                <div class="form-check form-check-inline">
                                                    <select class="custom-select" name="user_type">
                                                        <option value="">Select User Type</option>
                                                        @foreach($getusertype as $userType)

                                                        <option value="{{ $userType->id }}"
                                                            {{ $user->usertype == $userType->id ? 'selected' : '' }}>
                                                            {{ $userType->name }}
                                                        </option>
                                                        @endforeach
                                                    </select>

                                                </div>
                                            </div>

                                            <div class="col-md-6">
                                                <label class="required">Employee Code</label><br>
                                                <div class="form-check form-check-inline">
                                                    <input type="text" maxlength="10" class="form-control" id="empCodeId" name="employeeCode" value="{{ old('employeeCode', $user->employee_code) }}">
                                                </div>
                                            </div>

                                                <div class="col-md-6">
                                                    <label class="required">Select LOB</label><br>
                                                    <div class="form-check form-check-inline">
                                                        <select class="custom-select" name="lob_id[]" multiple>
                                                            @foreach($getLobs as $lob) <!-- Fetch all available LOBs -->
                                                            <option value="{{ $lob->id }}"
                                                                {{ in_array($lob->id, old('lob_id', $user->lobs->pluck('id')->toArray())) ? 'selected' : '' }}>
                                                                {{ $lob->lob }}
                                                            </option>
                                                            @endforeach
                                                        </select>
                                                    </div>
                                                </div>
                                    

                                            <div class="col-md-6">
                                                <label class="required">Role</label><br>
                                                <div class="form-check form-check-inline">
                                                    <select class="custom-select" name="role_id">
                                                        <option value="">select User role</option>
                                                        @foreach($user->roles as $role)

                                                        <option value="{{ $role->id }}" {{ $role->id == old('role_id', $user->role_id) ? 'selected' : '' }}>
                                                            {{ $role->name }}
                                                        </option>
                                                        @endforeach
                                                    </select>
                                                </div>
                                            </div>


                                            <div class="col-md-6">
                                                <label class="required">Qualification</label><br>
                                                <div class="form-check form-check-inline">
                                                    <select class="custom-select" name="qualification">
                                                        <option value="">select Qualification</option>
                                                        <option value="ssc" {{ 'ssc' == $user->qualification ? 'selected' : '' }}>ssc</option>
                                                        <option value="hsc" {{ 'hsc' == $user->qualification ? 'selected' : '' }}>hsc</option>
                                                        <option value="graduation" {{ 'graduation' == $user->qualification ? 'selected' : '' }}>graduation</option>
                                                    </select>
                                                </div>
                                            </div>
                                            <div class="col-md-6">
                                                <label class="required">Reporting To</label><br>
                                                <div class="form-check form-check-inline">
                                                    <select class="custom-select" name="reportingto">
                                                        <option value=""> select Reporting To</option>
                                                    </select>
                                                </div>
                                            </div>
                                        </div>
                                    </div>
                                </div>
                            </div>
                        </div>
                        <!-- /.card-body -->
                        <div class="card-footer">
                            <button type="submit" class="btn btn-dark">Submit</button>
                        </div>
                    </form>
                </div>
            </div>
        </div>
    </div>
</div>
<script src="{{asset('Js/user.js')}}"></script>
@endsection

