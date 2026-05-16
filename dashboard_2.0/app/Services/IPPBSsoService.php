<?php

namespace App\Services;

use App\Models\SSO;
use App\Models\User;
use App\Models\LobMaster;
use App\Models\TokenModel;
use App\Helpers\EncryptionHelper;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Log;

class IPPBSsoService
{
    public function processToken(string $accessToken, string $encryptedPayload)
    {
        Log::info("IPPBSso Request Received", [
            'token' => $accessToken,
        ]);
        //token check code here
      
        $secretKey = config('FT_KEY');

        $decrypted = ippb_decrypt_payload_sso($encryptedPayload , $secretKey);
        
        if (!$decrypted) {

            logApiRequestResponse(
                'loginTokenValidate',
                'POST',
                ippb_decrypt_payload_sso($encryptedPayload , $secretKey), 
                'Could not decrypt request_data.',
                500,
                '',
                'sso-login-token-validate'
            );

            return ippb_encrypted_error_response('Could not decrypt request_data.');
        }

        Log::info("IPPBSso Decrypted Payload", ['payload' => $decrypted]);

        $payload = json_decode($decrypted, true);
        
        if (!$payload || empty($payload['agent_id'])) {
            logApiRequestResponse(
                'loginTokenValidate',
                'POST',
                ippb_decrypt_payload_sso($encryptedPayload , $secretKey), 
                'Invalid request payload.',
                500,
                '',
                'sso-login-token-validate'
            );
            return ippb_encrypted_error_response('Invalid request payload.');
        }
        
        Log::info("IPPBSso Validated Payload", ['agent_id' => $payload['agent_id']]);

        $user = User::where('employee_code', $payload['agent_id'])->first();
        
        if (!$user) {
                logApiRequestResponse(
                'loginTokenValidate',
                'POST',
                ippb_decrypt_payload_sso($encryptedPayload , $secretKey), 
                'User not found.',
                500,
                '',
                'sso-login-token-validate'
            );
            return ippb_encrypted_error_response('User not found.');
        }

        $lob = $payload['lob'] ?? 'Dashboard';
        
        Log::info("IPPBSso Payload Validated", [
            'lob' => $lob,
            'user_id' => $user->id,
            'agent_id' => $payload['agent_id']
        ]);
        
        if ($lob === 'Dashboard') {

            $authToken = generateTokenAll($user);
            $url = config('Profile.Frontend.Url','https://uatdashboard-ippb.fynity.in') . '?xutm=' . $authToken;

            $flowMap = [
                'sell_now' => 'sell-now',
                'view_transaction' => 'PolicyStatusReport',
            ];
            if (!empty($payload['journey_type']) && isset($flowMap[$payload['journey_type']])) {
                $url .= '&flow=' . $flowMap[$payload['journey_type']];
            }
            return $this->success($url);
        }


            return [
                'status' => false,
                'encrypted_error' => ippb_encrypt_sso_payload(
                    json_encode(['message' => 'Unsupported LOB type.'])
                )
            ];
    }


    private function success(string $url)
    {
        return [
            'status' => true,
            'return_url' => $url
        ];
    }

    private function error(string $msg)
    {
        return [
            'status' => false,
            'message' => $msg
        ];
    }
}
