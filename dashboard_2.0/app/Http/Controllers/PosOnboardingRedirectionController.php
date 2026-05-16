<?php

namespace App\Http\Controllers;
use App\Http\Controllers\User\LoginController;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Str;
use Illuminate\Support\Carbon;
use App\Models\User;

class PosOnboardingRedirectionController extends Controller
{

    public function generatePosToken(Request $request)
    {

        $auth = Auth::user();
        $mobile = credential_decrypt($auth->mobile);

        $encryptedMobile = encrypt_decrypt_password_remote($mobile);

        $domainUrl = config('pos_onboarding_redirection_url');

        $response = Http::withHeaders([
            'Content-Type' => 'application/json',
        ])->post("{$domainUrl}/api/generate_pos_token", [
            'username' => config('pos_onboarding_token_username'),
            'password' => config('pos_onboarding_token_password'),
            'mobile'   => $encryptedMobile,
        ]);

        $responseData = $response->json();

        if ($responseData['status'] === 'true') {
            $redirectUrl = "{$domainUrl}/api/redirectUser?token={$responseData['token']}&data={$encryptedMobile}";

            return response()->json([
                'status' => 'true',
                'url'    => $redirectUrl,
            ]);
        } else {
            return response()->json([
                'status' => 'false',
                'message' => $responseData['message'] ?? 'Something went wrong.',
            ]);
        }
    }

    public function generateLoginToken(Request $request)
    {
        $data = $request->json()->all();

        if (empty($data['username']) || empty($data['password'])) {
            return response()->json([
                "status" => "false",
                "message" => "username & password field is required.",
                "token" => ""
            ]);
        }

        $validUsername = config('pos_onboarding_login_token_username');
        $validPassword = config('pos_onboarding_token_password');

        if ($data["username"] !== $validUsername || $data["password"] !== $validPassword) {
            return response()->json([
                "status" => "false",
                "message" => "Invalid username & password.",
                "token" => ""
            ]);
        }

        $uuidToken = (string) Str::uuid();

        DB::table('sso_api_tokens')->insert([
            'sso_api_token' => $uuidToken,
            'status'       => 'Y',
            'created_at'   => Carbon::now()
        ]);

        $response = [
            'status' => 'true',
            'token' => $uuidToken,
            'expires_at' => Carbon::now()->addMinutes(30)->format('d/m/Y h:i a'),
        ];

        return response()->json($response);
    }

    public function redirectLoginEmployee(Request $request)
    {
        $token = $request->query('token');
        $mobile = $request->query('data');

        if (empty($token) || empty($mobile)) {
            return response()->json(['status' => 'false', 'message' => 'Invalid Parameter']);
        }

        $record = DB::table('sso_api_tokens')
            ->where('sso_api_token', $token)
            ->where('status', 'Y')
            ->first();

        if (!$record) {
            return response()->json(['status' => 'false', 'message' => 'Invalid Access Token']);
        }

        $createdAt = Carbon::parse($record->created_at);
        if (now()->diffInMinutes($createdAt) > 30) {
            return response()->json(['status' => 'false', 'message' => 'Token Expired.']);
        }

        if ($record->status === 'N') {
            return response()->json(['status' => 'false', 'message' => 'Token Already Used']);
        }

        DB::table('sso_api_tokens')
            ->where('sso_api_token', $token)
            ->update(['status' => 'N']);

        $mobileD = encrypt_decrypt_password_remote($mobile, 'D');

        $mobiecheck  = credential_encrypt($mobileD);

        $user = User::where('mobile', $mobiecheck)->first();
        
        if (!$user) {
            return response()->json(['status' => false, 'message' => 'User not found.']);
        }
    
        $otp = config('revamp_otp_for_pos_redirection'); 
        $loginRequest = new Request([
            'user_name' => credential_decrypt($user->username),
            'otp' => $otp,
            'loginOption' => 'email_otp',
            'ip' => $request->ip(),
            'browser' => $request->header('User-Agent'),
        ]); 

        $loginController = new LoginController();
        $response = $loginController->verifyCustomerOtp($loginRequest);
        $responseData = $response->getData(true);

        if (isset($responseData['status']) && $responseData['status'] == 200 && !empty($responseData['access_token'])) {
            $accessToken = $responseData['access_token'];

            $redirectUrl = config('revamp_pos_redirection_url') . $accessToken;

            return response()->json([
                "status" => true,
                "message" => "URL generated successfully.",
                "return_url" => $redirectUrl
            ]);
        } else {
            return response()->json([
                "status" => false,
                "message" => $responseData['message'] ?? 'Something went wrong.',
                "return_url" => null
            ]);
        }
    }
}
