<?php

namespace App\Http\Controllers;

use App\Models\PartnerUserMapping;
use App\Models\ThemeMaster;

use Illuminate\Support\Facades\Validator;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;

// use Illuminate\Support\Facades\Auth;

class ThemeMasterController extends Controller
{
    protected $authUser;
    public function __construct()
    {
        $this->authUser = Auth::user();
        
    }
   
    public function storeTheme(Request $request)
    {
        $editPermission = "Theme Configurator.edit";
        if (!$this->authUser->can($editPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }
        $validator = Validator::make($request->all(), [
            'theme_value' => 'required|array',
            'theme_name' =>'required|string',
            'status' => 'required',
            'user_id' => 'nullable|integer'  
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }

        if ($request->status == 'Y') {
            ThemeMaster::where('status','Y')->update(['status'=>'N']);
        }

        $theme = new ThemeMaster();
        $theme->theme_value = $request->theme_value;  
        $theme->user_id = $request->user_id;
        $theme->theme_name = $request->theme_name;
        $theme->status = $request->status;
        $theme->save();

        return response()->json([
            'message' => 'Theme Stored Successfully',
            'data' => [
                $theme,
            ]
        ], 200);
    }
    public function updateTheme(Request $request)
    {
        $editPermission = "Theme Configurator.edit";
        if (!$this->authUser->can($editPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $validator = Validator::make($request->all(), [
            'theme_value' => 'required|array',
            'theme_name' =>'required|string',
            'status' => 'required',
            'user_id' => 'nullable|integer'  
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }
        $theme = ThemeMaster::find($request->id);

        if (!$theme) {
            return response()->json(['message' => 'Theme not found'], 404);
        }
        if ($request->status == 'Y') {
            ThemeMaster::where('status','Y')->where('id','!=',$theme->id)->update(['status'=> 'N']);
        }

        $theme->theme_value = $request->theme_value;  
        $theme->user_id = $request->user_id;
        $theme->theme_name = $request->theme_name;
        $theme->status = $request->status;
        $theme->save(); 

        return response()->json([
            'message' => 'Theme Updated Successfully',
            'data' => [
                $theme,
            ]
        ], 200);
    }
    public function getTheme(Request $request){

        // $editPermission = "Theme Configurator.view";
        // if (!$this->authUser->can($editPermission)) {
        //     return response()->json([
        //         'status' => false,
        //         'message' => 'You do not have permission to access this resource.',
        //     ], 403);
        // }

        $user_id = $this->authUser->id;
        // if(config('partner_login')){
            $partner_upper_ids = getUserUpperHierarchy($user_id);
            if(count($partner_upper_ids))
                $ids = array_column($partner_upper_ids, 'id');
            else 
                $ids = [];

            $partner_upper_ids = array_merge($ids, [$user_id]);
        // }
        if(count($partner_upper_ids)){
            $fetch_theme_id = PartnerUserMapping::whereIn('user_id',$partner_upper_ids)->pluck('theme_id')->first();
        }

        if($fetch_theme_id){
            $theme_data_single = ThemeMaster::where('id',$fetch_theme_id)->first();
            
            $theme_data = ThemeMaster::all()->map(function ($theme) use ($theme_data_single) {

                $theme->status = ($theme->id == $theme_data_single->id) ? 'Y' : 'N';
            
                return $theme;
            });

        }else{
            if (!$request->all()) {
                $theme_data = ThemeMaster::all();
                return response()->json($theme_data, 200);
            }
            $query = ThemeMaster::query();
    
            if ($user_id = $request->input('user_id')) {
                $query->where('user_id', $user_id);
            } else {
                return response()->json(null, 200);
            }
            if($theme_name = $request->input('theme_name')){
                $query->where('theme_name',$theme_name);
            }
            if($request->input('status') == 'Y'){
                $query->where('status','Y');
            }
            $theme_data = $query->get();
    
            if ($theme_data->isEmpty()) {
                $theme_data = ThemeMaster::where('status', 'Y')
                    ->where('user_id', 2)
                    ->get();
            }
        }
        
        return response()->json($theme_data,200);
    }

    public function deleteTheme(Request $request){

        $editPermission = "Theme Configurator.delete";
        if (!$this->authUser->can($editPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $theme = ThemeMaster::find( $request->id);
        $final = $theme->delete();
        if($final){
            return response()->json([
                'status' => 200,
                'return_data' => $theme,
                'message' => 'Theme Deleted Successfully'
            ]);
        }
    }
}
