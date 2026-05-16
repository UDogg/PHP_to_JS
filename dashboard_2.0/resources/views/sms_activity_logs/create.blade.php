@extends('layout.app', ['pageTitle' => 'SMS Logs', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
@section('content')
<div class="container">
    <h2>Add SMS</h2>

    @if(session('success'))
    <div class="alert alert-success alert-dismissible fade show" role="alert">
        {{ session('success') }}
        <button type="button" class="btn-close" data-bs-dismiss="alert" aria-label="Close"></button>
    </div>
    @endif

    @if(session('error'))
    <div class="alert alert-danger alert-dismissible fade show" role="alert">
        {{ session('error') }}
        <button type="button" class="btn-close" data-bs-dismiss="alert" aria-label="Close"></button>
    </div>
    @endif

    <form method="POST" action="{{ route('smsActivityLog.store') }}">
        @csrf

        <div class="mb-3">
            <label>Mobile</label>
            <input type="tel" name="mobile" class="form-control" value="{{ old('mobile') }}" minlength="10" maxlength=10 required>
            {{--  Error message --}}
            @error('mobile')
            <div class="text-danger mt-1">{{ $message }}</div>
            @enderror
        </div>

        <div class="mb-3">
            <label>Message</label>
            <textarea name="message" class="form-control" required>{{ old('message') }}</textarea>
        </div>

        <div class="mb-3">
            <label>Type</label>
            <input type="text" name="type" class="form-control" value="{{ old('type') }}" required>
        </div>

        <div class="mb-3">
            <label>Status</label>
            <input type="text" name="status" class="form-control" value="{{ old('status') }}" required>
        </div>

      {{-- <div class="mb-3">
            <label>Sent At</label>
            <textarea name="sent_at" class="form-control" required>{{ old('sent_at') }}</textarea>
        </div>
        --}}

        <div class="mb-3">
            <label>User ID</label>
            <input type="number" name="user_id" class="form-control" value="{{ old('user_id') }}" required>
        </div>

        <button type="submit" class="btn btn-primary">Submit</button>
        <a href="{{ route('smsActivityLog.index') }}" class="btn btn-secondary">Cancel</a>
    </form>
</div>

@endsection
