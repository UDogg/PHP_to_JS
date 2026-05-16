@extends('layout.app', ['pageTitle' => '', 'pageHeader' => '', 'menu' => '', 'subMenu' => ''])

@section('content')

<head>
    <meta name="csrf-token" content="{{ csrf_token() }}">
    <meta name="app-url" content="{{ url('/') }}">
</head>

<div style="max-width: 1000px; margin: 0 auto; padding: 20px;">
    <h3>Decrypt Payload</h3>
    <form method="POST" action="{{ route('decrypt.payload') }}">
        @csrf
        <div style="display: flex; gap: 20px;">
            <!-- Encrypted Payload -->
            <div style="flex: 1;">
                <label for="encrypted_payload" style="font-weight: bold;">Encrypted Payload</label><br>
                <textarea
                    name="encrypted_payload"
                    id="encrypted_payload"
                    rows="20"
                    style="width: 100%; padding: 10px; border: 1px solid #ccc; border-radius: 4px;"
                    placeholder="Paste encrypted payload here...">{{ old('encrypted_payload') ?? $encrypted ?? ""  }}</textarea><br><br>
                <button
                    type="submit"
                    style="padding: 8px 16px; background-color: #007bff; color: white; border: none; border-radius: 4px; cursor: pointer;">Decrypt</button>
            </div>

            <!-- Decrypted Output -->
            <div style="flex: 1;">
                <label style="font-weight: bold;">Decrypted Output</label><br>
                <div style="background-color: #f8f9fa; padding: 10px; border: 1px solid #ccc; border-radius: 4px; height: 500px; overflow: auto;">
                    @if(isset($decrypted) && $decrypted)
                    <pre style="white-space: pre-wrap; word-wrap: break-word;">{{ is_array($decrypted) ? json_encode($decrypted, JSON_PRETTY_PRINT) : $decrypted }}</pre>
                    @elseif(isset($decrypted))
                    <p style="color: #888;">No encrypted data found.</p>
                    @else
                    <p style="color: #aaa;">Decrypted output will appear here after submitting.</p>
                    @endif
                </div>
            </div>
        </div>
    </form>
</div>

<!-- //////////////////////////////////////////////////////////////////////////////////////////////////////////////// -->


<div style="max-width: 1000px; margin: 0 auto; padding: 20px;">
    <h3>Encrypt Data</h3>

    <form method="POST" action="{{ route('encrypt.request') }}">
        @csrf
        <div style="display: flex; gap: 20px;">
            <!--  Decrypted Payload -->
            <div style="flex: 1;">
                <label for="decrypted_data" style="font-weight: bold;">Decrepted Payload</label><br>
                <textarea
                    name="decrypted_data"
                    id="decrypted_data"
                    rows="20"
                    style="width: 100%; padding: 10px; border: 1px solid #ccc; border-radius: 4px;"
                    placeholder="Paste encrypted payload here...">{{ old('decrypted_data') ?? $decrypted_data ?? ""  }}</textarea><br><br>
                <button
                    type="submit"
                    style="padding: 8px 16px; background-color: #007bff; color: white; border: none; border-radius: 4px; cursor: pointer;">Encrypt</button>
            </div>

            
            <!-- Encrypted Output -->

            <div style="flex: 1;">
                <label style="font-weight: bold;">Encrypted Output</label><br>
                <div style="background-color: #f8f9fa; padding: 10px; border: 1px solid #ccc; border-radius: 4px; height: 500px; overflow: auto;">
                    @if(isset($encrypted_result) && $encrypted_result)
                    <pre id="encrypted_output" style="white-space: pre-wrap; word-wrap: break-word;">{{ $encrypted_result }}</pre>
                    @elseif(isset($decrypted))
                    <p style="color: #888;">No encrypted data found.</p>
                    @else
                    <p style="color: #aaa;">Encrypted output will appear here after submitting.</p>
                    @endif
                </div>
            </div>
        </div>
    </form>
</div>


@endsection




