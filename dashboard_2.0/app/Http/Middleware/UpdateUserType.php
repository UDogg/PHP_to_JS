<?php

namespace App\Http\Middleware;

use Closure;
use Illuminate\Http\Request;
use Symfony\Component\HttpFoundation\Response;
use Illuminate\Support\Facades\Auth;
use App\Models\UserMapping;


class UpdateUserType
{
    /**
     * Handle an incoming request.
     *
     * @param  \Closure(\Illuminate\Http\Request): (\Symfony\Component\HttpFoundation\Response)  $next
     */
    public function handle(Request $request, Closure $next): Response
    {
        if (Auth::check()) {
            $user = Auth::user();
            
            $token = $request->user()->currentAccessToken();
             if ($token) {
                $switch     = getParsedAbilityValue($token, 'switch:');
                $usertype   = getParsedAbilityValue($token, 'usertype:');

                 if ($switch =="true") {
                    $user->usertype = $usertype;
                    if ($user->usertype !=1) {
                    $mappedUser = UserMapping::where('user_id', $user->id)
                                    ->where('user_type', $user->usertype)
                                    ->first();
                     $user->employee_code=$mappedUser->employee_code;
                     $user->reportingto=$mappedUser->reportingto;
                    }
                }
            }
        }
        return $next($request);
    }
}
