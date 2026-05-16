<?php

namespace App\Http\Controllers;

use App\Http\Requests\lobUpdate;
use App\Models\lobMaster as lob_master ;
use Database\Seeders\lob_master_seeder;
use Illuminate\Http\Request;

class LobMasterController extends Controller
{
    //
    public static function index()
    {
        $lobs = lob_master::get()->all();

        return view('lob_master', compact('lobs'));
    }
    public static function update(lobUpdate $request)
    {
        $action = $request->action;
        if($action == 'add')
        {
            $str = 'Y';
        }
        else
        {
            $str = 'N';
        }
        $selected_lobs = $request->lobs;
        $update = lob_master::where('id', $selected_lobs)->update(['is_enabled' => $str]);
        if ($update) {
            return json_encode(['code' => 200, 'success' => 'Lob Master Updated Successfully']);
        }
        else
        {
            return json_encode(['code' => 400, 'error' => 'Something went wrong']);
        }


    }
        public  function show(Request $request)
        {
            if($request->has('show_lob_categorywise') && config('show_lob_category_name')){
                $lobs = lob_master::where('is_enabled', 'Y')->select('lob_category_name')->distinct()->pluck('lob_category_name')->values()
                            ->map(function ($lob, $index) {
                                return [
                                    'id' => $index + 1,
                                    'name' => $lob
                                ];
                            })->toArray();
            }else{
                $lobs = lob_master::select('id','lob as name','lob_name','lob_master_name')->where('is_enabled','Y')->get();
            }
            return  requestResponseMessage(['status' => 200,'data'=>$lobs,'message'=>'All Line of Bussiness List']);
        }

        //club lob
        public function lobClub(Request $request){
            $lobs = lob_master::whereRaw('LOWER(lob) = ?', [strtolower($request->lob)])->orwhereRaw('LOWER(lob_master_name) = ?', [strtolower($request->lob_name)])->get();
            if ($lobs->isEmpty()) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'LOB does not exist'
                ], 500);
            }

            foreach($lobs as $lob) {
                if ($lob) {
                        // Only retrieve the updated LOB data
                        $groupedLobs = lob_master::select('id', 'lob_master_name', 'lob','productsubtype_id')
                            ->whereRaw('LOWER(lob) = ?', [strtolower($request->lob)]) 
                            ->orwhereRaw('LOWER(lob_master_name) = ?', [strtolower($request->lob_name)])
                            ->get()
                            ->groupBy('lob_master_name');

                        return response()->json([
                            'status' => 200,
                            'return_data' => $groupedLobs,
                            'message' => 'Lob Master data fetched Successfully'
                        ], 200);
                } else {
                    return response()->json([
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'LOB not found'
                    ], 500);
                }
            }
        }
}
