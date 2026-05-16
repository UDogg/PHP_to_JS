<?php

namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;
use App\Models\KeyUtility;
use App\Models\MaskConfiguration;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use App\Models\lobMaster as lob_master;

class MaskConfiguratorController extends Controller
{
    public function index(Request $request){
        $maskConfigurator = MaskConfiguration::all();
       
        $lobs = lob_master::select('id','lob_name','lob')->where('is_enabled','Y')->get();
        $lobs_arr = array();
        foreach ($lobs as $key => $value)
        {
            array_push($lobs_arr,$value->id);
        }
        if(!empty($request->search)){
            $columns = DB::table('policystatus_column_master')->whereIn('lob',$lobs_arr)->where('column_name','LIKE','%'.$request->search.'%')->get()  ;
            $key_name = KeyUtility::select('id','key')->where('key','LIKE','%'.$request->search.'%')->get()->all();
        }
        else
        {
            $columns = DB::table('policystatus_column_master')->whereIn('lob',$lobs_arr)->get()  ;
            $key_name = KeyUtility::select('id','key')->get()->all();
        }
        return view('maskConfiguration', compact('maskConfigurator','key_name'));
    }
    public function maskConfiguratoradd(Request $request){
        $rules=[
            'key_name' => 'required',
            'masking_position' => 'required',
            'masking_symbol' => 'required',
        ];
        $validator = Validator::make($request->all(), $rules);
        if($validator->fails()){    
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
            $insert = new MaskConfiguration();
            $insert->key_name = $request->key_name;
            $insert->masking_position = $request->masking_position;
            $insert->masking_symbol = $request->masking_symbol;
            $insert->save();
            if($insert){
                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => 'Mask Configuration Added Successfully',
                    ],
                    200
                );
            }else{
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Something went wrong',
                    ],
                    500
                );
            }
        }

    }
     public function create(){
        return view('mask_configurator.create');
     }
    public function maskConfiguratorGetData(Request $request){
        $data = MaskConfiguration::get();
        if($data){
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'Data Added successfully',
                ],
                200
            );
        }else{
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Something went wrong',
                ],
                500
            );
        }
    }
    public function destroy(Request $request)
    {
        $mask_configurator_data = MaskConfiguration::where('id', $request->id)->first();
        if ($mask_configurator_data) {
            $mask_configurator_data->delete();
            return response()->json([
                'status' => 200,
                'return_data' => [$mask_configurator_data],
                'message' => 'Company Data deleted successfully']);
        } else {
            return response()->json([
                'status' => '500',
                'return_data' => [],
                'message' => 'Company Data not found or already deleted'
            ]);
        }
    }
}
