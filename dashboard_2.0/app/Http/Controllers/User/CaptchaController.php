<?php

namespace App\Http\Controllers\User;

use App\Http\Controllers\Controller;
use App\Models\Broker;
use App\Models\User;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use Mews\Captcha\Facades\Captcha;

class CaptchaController extends Controller
{
    public function reloadCaptcha()
    {
        return response()->json(['captcha' => Captcha::img()]);
    }
    public function checkCaptcha(Request $request)
    {
        $broker=Broker::first();
        $user = User::where('email', credential_encrypt($request->email))->first();
        if($user){
            $rules = [
                'email' => ['required', 'email'],
            ];
            $messages = [];
            if ($broker->captacha_configure== 'On') {
                $rules['captcha'] = 'required|captcha';
                $messages = [
                    'captcha.required' => 'Captcha is required.',
                    'captcha.captcha' => 'Please enter a valid captcha.',
                ];
            }
            $validator = Validator::make( $request->all(), $rules, $messages );
            if ($validator->fails()) {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'validations fails',
                            'errors' => $validator->errors()
                        ],
                        500
                    );
            }else{
                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => 'Captcha Verified',
                    ],
                    200
                );
            }
        }else{
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid User',
                ],
                500
            );
        }
    }

    // }

}
