<?php

namespace App\Http\Controllers;

use App\Models\lobMaster;
use App\Models\SellNow;
use App\Models\User;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;

class SellNowController extends Controller
{
    public function sellNowUserType(Request $request)
    {
        $lobs = lobMaster::where('id',$request->lob_id)->get();
        if ($lobs->isEmpty()) {

            return response()->json([
                'success' => 500,
                'return_data' => [],
                'message' => 'No LOB found for the provided ID.',
            ], 500);
        }

        foreach($lobs as $lob){
            $user= Auth::user();
                $lob = SellNow::insert([
                    "user_id" =>$user->id,
                    "lob_id" => $request->lob_id
                ]);
                if($lob) {
                    return response()->json([
                        'success' => 200,
                        'return_data'=>$lob,
                        'message' => "lob created successfully"
                    ],200);
                } else {
                    return response()->json([
                        'success' => 500,
                        'return_data'=>[],
                        'message' => "something went wrong"
                    ],500);
                }
        }

    }
    public function LoginUserLobList(Request $request){
           
        if($request->has('user_id')){
            $user = User::find(credential_decrypt($request->user_id));
        }else{
            $user = Auth::user();
        }
        
        $show_pos_popup = config('show_pos_popup'); 
        $allLobs = lobMaster::select('id as lob_id','redirect_insame_tab','lob_name','lob','is_enabled','lob_master_name','frontend_url','lob_icon')->where('is_enabled','Y')->get()->all();

        if($user->usertype == 5 && config('Allow.Customer.Email.Login')=="true" && config('Change.Url.Redirection') == "true"){
            $modifiedLobs = [];
            foreach ($allLobs as $lob) {

                if ($lob->lob == 'CAR') {
                    $frontendUrl = config('Corporate.Sell.Now.Redirection.Car') ?? $lob->frontend_url;
                } elseif ($lob->lob === 'BIKE' ) {
                    $frontendUrl = config('Corporate.Sell.Now.Redirection.Bike') ?? $lob->frontend_url;
                } else {
                    $frontendUrl = $lob->frontend_url; 
                }
                $modifiedLobs[] = [
                    'lob_id'             => $lob->lob_id,
                    'redirect_insame_tab' => $lob->redirect_insame_tab,
                    'lob_name'           => $lob->lob_name,
                    'lob'                => $lob->lob,
                    'is_enabled'         => $lob->is_enabled,
                    'lob_master_name'    => $lob->lob_master_name,
                    'frontend_url'       => $frontendUrl,
                    'lob_icon'           => $lob->lob_icon,
                ];
            }
            $allLobs = collect($modifiedLobs)->unique('lob_id')->values();
        } else {
            $allLobs = collect($allLobs)->unique('lob_id')->values();
        }

        if ($user->usertype == "5") {
            return response()->json([
                'success' => 200,
                'return_data' => $allLobs,
                'show_pos_popup' => $show_pos_popup,
                'message' => "List of Lob of Login User"
            ], 200);
        }

        $show_enable_lob = strtolower(config('show_enable_lob'));

        if($show_enable_lob != 'yes'){
            $lobs = SellNow::Join('lob_master','lob_master.id','user_lob_relation.lob_id')
            ->select('lob_master.id as lob_id','lob_master.lob_name','lob_master.lob','lob_master.is_enabled','lob_master.lob_master_name','lob_master.lob_category_name','lob_master.frontend_url','lob_master.lob_icon')
            ->where('user_lob_relation.user_id',$user->id)
                ->where('lob_master.is_enabled','Y')
            ->get();
        }else{
            $lobs = $allLobs;
        }
       
        $channel = $user->channel;
        $category = $user->category_id;
        $rm_branch_code = $user->rm_branch_code;

        $lobs = collect($lobs)->unique('lob_id')->values();
        if (!$lobs->isEmpty()) {
            return response()->json([
                'success' => 200,
                'return_data' => $lobs,
                'show_pos_popup' => $show_pos_popup,
                'channel' => $channel,
                'category' => $category,
                'rm_branch_code' => $rm_branch_code,
                'message' => "List of Lob of Login User"
            ], 200);
        } else {
            return response()->json([
                'success' => 200,
                'return_data' => $allLobs,
                'show_pos_popup' => $show_pos_popup,
                'channel' => $channel,
                'category' => $category,
                'rm_branch_code' => $rm_branch_code,
                'message' => "List of Lob of Login User"
            ], 200);
        }
    }


    public function OfflineUploadLobList(Request $request){
           
        if($request->has('user_id')){
            $user = User::find(credential_decrypt($request->user_id));
        }else{
            $user = Auth::user();
        }
        
        $show_pos_popup = config('show_pos_popup'); 
        
        $allLobs = lobMaster::select('id as lob_id','redirect_insame_tab','lob_name','lob','is_enabled','lob_master_name','lob_category_name','frontend_url','lob_icon')->where('is_enabled','Y')->get()->all();
        
        if($user->usertype == 5 && config('Allow.Customer.Email.Login')=="true" && config('Change.Url.Redirection') == "true"){
            $modifiedLobs = [];
            foreach ($allLobs as $lob) {

                if ($lob->lob == 'CAR') {
                    $frontendUrl = config('Corporate.Sell.Now.Redirection.Car') ?? $lob->frontend_url;
                } elseif ($lob->lob === 'BIKE' ) {
                    $frontendUrl = config('Corporate.Sell.Now.Redirection.Bike') ?? $lob->frontend_url;
                } else {
                    $frontendUrl = $lob->frontend_url; 
                }
                $modifiedLobs[] = [
                    'lob_id'             => $lob->lob_id,
                    'redirect_insame_tab' => $lob->redirect_insame_tab,
                    'lob_name'           => $lob->lob_name,
                    'lob'                => $lob->lob,
                    'is_enabled'         => $lob->is_enabled,
                    'lob_master_name'    => $lob->lob_master_name,
                    'frontend_url'       => $frontendUrl,
                    'lob_icon'           => $lob->lob_icon,
                ];
            }
            $allLobs = collect($modifiedLobs)->unique('lob_id')->values();
        } else {
            $allLobs = collect($allLobs)->unique('lob_id')->values();
        }

        if ($user->usertype == "5") {
            return response()->json([
                'success' => 200,
                'return_data' => $allLobs,
                'show_pos_popup' => $show_pos_popup,
                'message' => "List of Lob of Login User"
            ], 200);
        }

        $show_enable_lob = strtolower(config('show_enable_lob'));

        if($show_enable_lob != 'yes'){
            $lobs = SellNow::Join('lob_master','lob_master.id','user_lob_relation.lob_id')
            ->select('lob_master.id as lob_id','lob_master.lob_name','lob_master.lob','lob_master.is_enabled','lob_master.lob_master_name','lob_master.lob_category_name','lob_master.frontend_url','lob_master.lob_icon')
            ->where('user_lob_relation.user_id',$user->id)
            ->where('lob_master.is_enabled','Y')
            ->get();
        }else{
            $lobs = $allLobs;
        }
       
        $channel = $user->channel;
        $category = $user->category_id;
        $rm_branch_code = $user->rm_branch_code;

        $lobs = collect($lobs)->unique('lob_id')->values();
        if (!$lobs->isEmpty()) {
            return response()->json([
                'success' => 200,
                'return_data' => $lobs,
                'show_pos_popup' => $show_pos_popup,
                'channel' => $channel,
                'category' => $category,
                'rm_branch_code' => $rm_branch_code,
                'message' => "List of Lob of Login User"
            ], 200);
        } else {
            return response()->json([
                'success' => 200,
                'return_data' => $allLobs,
                'show_pos_popup' => $show_pos_popup,
                'channel' => $channel,
                'category' => $category,
                'rm_branch_code' => $rm_branch_code,
                'message' => "List of Lob of Login User"
            ], 200);
        }
    }

    public function posList(Request $request)
    {
        $user = Auth::user();
        $userId = $user->id;

        // $allUsers=getUserLowerHierarchy($userId, $user->usertype);
        
        // $empcodes = array_column( $allUsers, 'employee_code'); 
        // $empcodes[] = $user->employee_code;

        if (empty($userId)) {
            return response()->json([
                'success' => false,
                'return_data' => [],
                'message' => 'No user ID provided.',
            ], 400);
        }

        $users = User::select('username','name','middle_name','last_name','mobile', 'id AS userId')
            ->where('employee_code' , $user->employee_code)
            ->where('usertype', '2')
            ->get();
           
        if ($users->isEmpty()) {
            return response()->json([
                'success' => false,
                'return_data' => [],
                'message' => 'No users found.',
            ], 404); 
        }

        $decryptedUsers = $users->map(function ($user) {
            return [
                'id' => $user->userId,
                'username' => credential_decrypt($user->name).' '.credential_decrypt($user->middle_name).' '.credential_decrypt($user->last_name).'-'.credential_decrypt($user->mobile),
            ];
        });

        return response()->json([
            'success' => true,
            'count' => $decryptedUsers->count(),
            'return_data' => $decryptedUsers,
            'message' => 'Users fetched successfully.',
        ], 200); 
    }
}
