<?php

namespace App\Http\Controllers\CustomerController;

use App\Http\Controllers\Controller;
use App\Http\Requests\StorePolicyExpireRequest;
use Illuminate\Http\Request;
use App\Models\CustomerPolicyExpire;
use Illuminate\Container\Attributes\Auth;

class PolicyExpireController extends Controller
{
    public function store(StorePolicyExpireRequest $request)
    {
     
        foreach ($request->policy_details as $policy) {
            CustomerPolicyExpire::updateOrCreate([
                'customer_id' => $request->user_id,
                'lob_id' => $policy['lob_id'],
                'mobile_no' => $request->mobile_no ?? null, 
                'policy_no' => $policy['policy_no'] ?? null,
                'policy_end_date' => $policy['policy_end_date'] ?? null,
            ]);
        }

        return response()->json(['message' => 'Policies inserted successfully.'], 200);
    }
}
