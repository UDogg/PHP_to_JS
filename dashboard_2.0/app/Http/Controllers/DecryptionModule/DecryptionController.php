<?php

namespace App\Http\Controllers\DecryptionModule;

use App\Http\Controllers\Controller;
use Illuminate\Http\Request;

class DecryptionController extends Controller
{
    public function index()
    {
        return view('decrypt-payload');
    }

    public function decrypt(Request $request)
    {
        $encrypted = $request->input('encrypted_payload');

        try {
            $decrypted = getDecryptedPayload($encrypted);
            $result = json_decode($decrypted, true) ?: $decrypted;

        } catch (\Exception $e) {
            $result = 'Decryption failed: ' . $e->getMessage();
        }

        return view('decrypt-payload', [
            'decrypted' => $result,
            "encrypted" => $encrypted,
        ]);
    }

    public function encrypt(Request $request)
    {
        $decryptData = $request->input('decrypted_data');

        try {
            $newEncryptedData = getEncryptedPayload($decryptData);
            $result = json_decode($newEncryptedData, true) ?: $newEncryptedData;

        } catch (\Exception $e) {
            $result = 'Encryption failed: ' . $e->getMessage();
        }

        return view('decrypt-payload', [
            'decrypted_data' => $decryptData,
            "encrypted_result" => $result,
        ]);
    }


}


