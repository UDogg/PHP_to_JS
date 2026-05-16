<?php

namespace App\Http\Controllers;

use App\Models\KeyUtility;
use App\Models\keyUtilityMapping;
use App\Models\lobMaster as lob_master;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use function MongoDB\BSON\toJSON;

class KeyUtilityController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index(Request $request)
    {

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
        $key_utility_data = keyUtilityMapping::select('key_utility_mapping.id','key_utility_mapping.mapping_id','key_utility_mapping.lob','key_utility_mapping.key_id','c.column_name','b.lob','c.alias')->join('lob_master as b','b.id','key_utility_mapping.lob')->join('policystatus_column_master as c','c.id','key_utility_mapping.mapping_id')->get();
        return view('key_Utility',compact('lobs','columns','key_utility_data','key_name'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        //
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $validate = $request->validate([
            'key_name' => 'required|string|max:100',
        ]);
        if($validate){
            $insert_key = KeyUtility::create([
                'key' => $request->key_name
            ]);
            $key_id = $insert_key->id;
            if($insert_key){
                $lobs = lob_master::select('id','lob_name','lob')->where('is_enabled','Y')->get()->all();
                foreach ($lobs as  $value) {
                    $req_data = 'columns'.$value->id;
                    $data = !empty($request->$req_data) ? $request->$req_data : [];
                    $lob_id  = $value->id;
                    if(!empty($data))
                    {
                        foreach ($data as $val)
                        {
                            $insert_mappings = keyUtilityMapping::create([
                                'mapping_id' => $val,
                                'lob' => $lob_id,
                                'key_id' => $key_id
                            ]);
                        }
                    }
                }
               return response()->json(['status' => 200, 'message' => 'Key created successfully']);
            }
            else{
                return response()->json(['status' => 500, 'message' => 'Something went wrong']);
            }
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        //
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit($id)
    {
        $keyUtility = KeyUtility::find($id);
        if (!$keyUtility) {
            return response()->json(['status' => 404, 'message' => 'Key not found'], 404);
        }
    
        $mappings = keyUtilityMapping::where('key_id', $id)->get();
        return response()->json([
            'key_id' => $keyUtility->id,
            'key_name' => $keyUtility->key,
            'mappings' => $mappings,
        ]);
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {

        $update_key_master = KeyUtility::where('id',$id)->update(['key' => $request->key_name]);
        if($update_key_master)
        {
            $lobs = lob_master::select('id','lob_name','lob')->where('is_enabled','Y')->get()->all();
            foreach ($lobs as  $value) {
                $req_data = 'columns'.$value->id;
                $data = !empty($request->$req_data) ? $request->$req_data : [];
                $lob_id  = $value->id;
                if(!empty($data))
                {
                    foreach ($data as $val)
                    {
                        $insert_mappings = keyUtilityMapping::create([
                            'mapping_id' => $val,
                            'lob' => $lob_id,
                            'key_id' => $id
                        ]);
                    }
                }
            }
            return response()->json(['status' => 200, 'message' => 'Key updated successfully']);
        }
        else
        {
            return response()->json(['status' => 500, 'message' => 'Something went wrong']);
        }
//        update keymappings
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id,Request $request)
    {
        if(!empty($request->mode))
        {
            $del_key_master = KeyUtility::where('id',$id)->delete();
            if($del_key_master)
            {
                $del_mappings  = keyUtilityMapping::where('key_id',$id)->delete();
                return response()->json(['status' => 200, 'message' => 'Key deleted successfully']);
            }
            else
            {
                return response()->json(['status' => 500, 'message' => 'Something went wrong']);
            }
        }
        $del_cols = keyUtilityMapping::where('id',$id)->delete();
        if($del_cols)
        {
            return response()->json(['status' => 200, 'message' => 'Key deleted successfully']);
        }
        else
        {
            return response()->json(['status' => 500, 'message' => 'Something went wrong']);
        }

    }
}
