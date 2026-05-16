<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use App\Models\lobMaster;
use App\Models\SellNow;


class LobClubListController extends Controller
{
    public function LoginUserUniqueLobList(Request $request){
        $user = Auth::user();
        $allLobs = lobMaster::where('is_enabled', 'Y')
            ->pluck('lob_master_name')
            ->unique()
            ->values();

        $userLobs = SellNow::join('lob_master', 'lob_master.id', 'user_lob_relation.lob_id')
            ->where('user_lob_relation.user_id', $user->id)
            ->where('lob_master.is_enabled', 'Y')
            ->pluck('lob_master.lob_master_name')
            ->unique()
            ->values();
    
        if (!$userLobs->isEmpty()) {
            return response()->json([
                'success' => 200,
                'return_data' => $userLobs,
                'message' => "List of unique Lob names for Login User"
            ], 200);
        } else {
            return response()->json([
                'success' => 500,
                'return_data' => $allLobs,
                'message' => "No Lobs found"
            ], 500);
        }
    }
    
}