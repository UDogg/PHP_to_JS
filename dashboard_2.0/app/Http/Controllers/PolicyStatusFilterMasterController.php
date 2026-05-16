<?php

namespace App\Http\Controllers;

use App\Http\Requests\policyFilterMasterReq;
use App\Models\lobMaster;
use App\Models\PolicyStatusColumnMaster;
use App\Models\PolicyStatusFilterMaster;
use App\Models\StagemasterModel;
use Illuminate\Http\Request;

class PolicyStatusFilterMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {

        $lobs = lobMaster::select('id','lob_name','lob')->where('is_enabled','Y')->get()->all();
        $stages = StagemasterModel::select('id','stage_name')->get()->all();
        $allData = PolicyStatusFilterMaster::select('filtername','key','value','lm.lob', 'policy_status_filter_master.id')->join('lob_master as lm','lm.id','policy_status_filter_master.lob')->get()->toArray() ?? [];
        $count = count($allData);
        $dataCollection = collect($allData);
        $res=$dataCollection->groupBy('filtername');
        return view('PolicyStatusFilterMaster',compact('lobs','stages','allData', 'count'));
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
    public function store(policyFilterMasterReq $request)
    {
        $name = $request->filter_name ?? null;
        $type  = $request->filter_type ?? null;
        $lob = $request->lob ?? [];
        $lob_val = implode(",", $lob);
        $key = $request->key ?? null;
        $value = $request->value ?? null;
        $columns = $request->columns ?? null;
     

           $data[] = [
               'filtername' => $name,
               'type' => $type,
               'lob' => $lob_val,
               'key' => $key,
               'value' => $value,
                'column' => $columns
           ];
      
        $insert = PolicyStatusFilterMaster::insert($data);
        if($insert)
        {
            return response()->json([
                'status' => 200,
                'message' => 'Filter Added Successfully'
            ]);
        }
        else
        {
            return response()->json([
                'status' => 503,
                'message' => 'Something went wrong'
            ]);
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
    // public function edit(string $id)
    // {
    //     //
    // }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request)
    {
        
        $data = PolicyStatusFilterMaster::find($request->id);
        $data->filtername = $request->name;
        $data->key = $request->key;
        $data->value = $request->value;
        $data->save();
    
        return response()->json(['success' => 'Data updated successfully']);
    }

    public function delete($id) 
    {
        $PolicyStatusFilterMaster = PolicyStatusFilterMaster::find($id);
    
        if (!$PolicyStatusFilterMaster) {
            return response()->json(['error' => 'Record not found'], 404);
        }
    
        $PolicyStatusFilterMaster->delete();
    
        return response()->json(['success' => 'Data deleted successfully']);
    }
    /**
     * Remove the specified resource from storage.
     */
    // public function destroy(string $id)
    // {
    //     //
    // }

    public function GetColumns(Request $request)
    {
        $validate = $request->validate([
            'lob' => 'array',
        ]);
        $dbColumns = !empty($request->lob) ? PolicyStatusColumnMaster::select('id','column_name')->whereIn('lob',$request->lob)->get()->toArray() : [];
        return response()->json([
            'status' => 200,
            'data' => $dbColumns
        ]);
    }
}
