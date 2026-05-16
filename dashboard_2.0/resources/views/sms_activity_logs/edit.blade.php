@extends('layout.app', ['pageTitle' => 'SMS Logs', 'pageHeader' => 'Menu', 'menu' => 'Menu', 'subMenu' => 'Menu'])
@section('content')
<div class="container">
    <h2>Edit SMS Log #{{ $log->id }}</h2>

    <form method="POST" action="{{ route('smsActivityLog.Update', $log->id) }}">
        @csrf
        @method('PUT')

        <div class="mb-3">
            <label>Mobile</label>
            <input type="tel" name="mobile" class="form-control" minlength="10" maxlength="10" value="{{ old('mobile', $log->mobile) }}" required>
            @error('mobile')
            <div class="text-danger mt-1">{{ $message }}</div>
            @enderror
        </div>

        <div class="mb-3">
            <label>Message</label>
            <textarea name="message" class="form-control" required>{{ old('message', $log->message) }}</textarea>
        </div>

        <div class="mb-3">
            <label>Type</label>
            <input type="text" name="type" class="form-control" value="{{ old('type', $log->type) }}" required>
        </div>

        <div class="mb-3">
            <label>Status</label>
            <input type="text" name="status" class="form-control" value="{{ old('status', $log->status) }}" required>
        </div>

        <div class="mb-3">
            <label>Sent At</label>
            <textarea name="sent_at" class="form-control" required>{{ old('sent_at', $log->sent_at) }}</textarea>
        </div>

        <div class="mb-3">
            <label>User ID</label>
            <input type="number" name="user_id" class="form-control" value="{{ old('user_id', $log->user_id) }}" required>
        </div>

        <button type="submit" class="btn btn-primary">Update Log</button>
        <a href="{{ route('smsActivityLog.index') }}" class="btn btn-secondary">Cancel</a>
    </form>
</div>

@endsection


