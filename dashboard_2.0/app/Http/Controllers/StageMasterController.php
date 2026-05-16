<?php

namespace App\Http\Controllers;

use App\Http\Requests\DelSubstage;
use App\Http\Requests\EditSubStage;
use App\Http\Requests\PriorityReq;
use App\Http\Requests\StageMaster;
use App\Http\Requests\SubStageReq;
use App\Models\lobMaster as lob_master;
use App\Models\StagemasterModel;
use App\Models\substagemaster;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;

class StageMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function __construct()
    {
        $this->user = Auth::user();
        if (!$this->user->can('stagemaster.view')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
    }
    public function index(Request $request)
    {
        $search_val = $request->search_val;
        $stage_masters = $count_stage = '';
        $per_page = $request->per_page ? $request->per_page : 10;
        $count_stage = StagemasterModel::count();
        if($request->has('search_val') && !empty($request->search_val))
        {
            $stageMasters = StagemasterModel::select('id','stage_name','sub_stage_name','priority')->where('stage_name', 'like', '%'.$request->search_val.'%')->orwhere('sub_stage_name', 'like', '%'.$request->search_val.'%')->paginate($per_page);
        }
        else
        {
            $stageMasters = StagemasterModel::select('id','stage_name','sub_stage_name','priority')->paginate($per_page);
        }
        $selectStage = StagemasterModel::all();
        $stageMaster = !empty($stageMasters) ? $stageMasters : '';
        $sub_stage_master = substagemaster::get()->toArray();
        $renewalcollection = collect($sub_stage_master);
        $renewal_stages = $renewalcollection->filter(function ($value, $key) {
            return $value['is_renewal'] == 'Y';
        });
        $renewal_stages->all();
        $renewal_stages = array_column($renewal_stages->all(), 'sub_stage_name','id');
        $sub_stage_master = (array_column($sub_stage_master, 'sub_stage_name','id'));


        return view('Stage_master' , compact('stageMaster', 'count_stage', 'selectStage', 'sub_stage_master','search_val','renewal_stages'));
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
    public function store(StageMaster $request)
    {
        if (!$this->user->can('stagemaster.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
//        check if alredy exist
        $count = StagemasterModel::count()+1;
        $check = StagemasterModel::select('stage_name')->where('stage_name', $request->stage_name)->first();
        if(!empty($check))
        {
            return json_encode(['code' => 503, 'error' => 'Stage Already Exist']);
        }
        $data = StagemasterModel::create([
            'stage_name' => $request->stage_name,
            'priority' => $count
        ]);
        if($data)
        {
            return json_encode(['code' => 200, 'success' => 'Stage Created Successfully']);
        }
        else
        {
            {
                return json_encode(['code' => 503, 'error' => 'Stage Not Created']);
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
    public function edit(string $id)
    {
        //

    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        if (!$this->user->can('stagemaster.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $data = StagemasterModel::where('id', $id)->update(['stage_name' => $request->edt_stage]);
        if($data)
        {
            return response()->json(['code' => 200, 'success' => 'Stage Updated Successfully']);
        }
        else
        {
            {
                return response()->json(['code' => 503, 'error' => 'Stage Not Updated Please Try Again']);
            }
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        //
        if (!$this->user->can('stagemaster.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $stage_masters = StagemasterModel::where('id', $id)->delete();
        if($stage_masters)
        {
            return json_encode(['code' => 200, 'success' => 'Stage Deleted Successfully']);
        }
        else
        {
            return json_encode(['code' => 503, 'error' => 'Stage Not Deleted']);
        }
    }
    public function create_subStage(SubStageReq $request)
    {
        if (!$this->user->can('stagemaster.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $new_sub_stage = '';
        if($request->has('action'))
        {
            if($request->action == 'new')
            {
                $new_sub_stage = substagemaster::create([
                   'sub_stage_name' => $request->new_substage_val
                ]);
                if($new_sub_stage)
                {
                    return response()->json(['code' => 200, 'success' => 'Sub Stage Created Successfully']);
                }
                else
                {
                    return response()->json(['code' => 503, 'error' => 'Sub Stage Not Created']);
                }
            }
        }
        else
        {
            $sub_stage_arr = '';
            $sub_stages_data = $add_comma ='';
            $sub_stage_arr = StagemasterModel::where('id', $request->stage_mstr)->first();
            $all_sub_stages = explode(',', $sub_stage_arr->sub_stage_name);
            if(in_array($request->sub_stage_name, $all_sub_stages))
            {
                return response()->json(['code' => 503, 'error' => 'Sub Stage Already Exist']);
            }
            else
            {
                $all_sub_stages[] = $request->sub_stage_name;
                $sub_stages_data = implode(',', $all_sub_stages);
//                dd($sub_stages_data);
    //           $add_comma = !empty($sub_stage_arr->sub_stage_name) ? ',' : '';
//                $sub_stages_data = $request->sub_stage_name.$add_comma.$sub_stage_arr->sub_stage_name;
                $sub_stage_arr->sub_stage_name = $sub_stages_data;
                $sub_stage_arr->save();
                return response()->json(['code' => 200, 'success' => 'Sub Stage Created Successfully']);
            }
        }

    }
//    public function edit_subStage(EditSubStage $request)
//    {
//        if (!$this->user->can('stagemaster.edit')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
//        $stage_id = $request->mdl_stg_id;
//        $new_sub_stage = $request->mdl_sb_stg;
//        $old_sub_stage = $request->mdl_sb_stg_old;
//        $sub_stages_data = $add_comma ='';
//        $sub_stage_arr = StagemasterModel::where('id', $stage_id)->first();
//        $add_comma = !empty($sub_stage_arr) ? ',' : '';
//        $sub_stages_data = str_replace($old_sub_stage, $new_sub_stage, $sub_stage_arr->sub_stage_name);
//        $sub_stage_arr->sub_stage_name = $sub_stages_data;
//        $sub_stage_arr->save();
//        return json_encode(['code' => 200, 'success' => 'Sub Stage Updated Successfully']);
//    }
    public function delete_subStage(DelSubstage $request)
    {
        $stage_id = $request->mdl_stg_id;
        $sub_Stage =  $request->mdl_sb_stg_old;
        $sub_stage_id = $request->mdl_sub_stg_id;
        $sub_stage_arr = StagemasterModel::where('id', $stage_id)->first();
        $str_sub_stage = $sub_stage_arr->sub_stage_name;
        $str_sub_stage = !empty($str_sub_stage) ? explode(',', $str_sub_stage) : '';
//        dd($str_sub_stage, $stage_id);
        if(in_array($sub_stage_id, $str_sub_stage))
        {
            $res_key = array_search($sub_stage_id,$str_sub_stage);

            unset($str_sub_stage[$res_key]);
        }
        else
        {
            return response()->json(['code' => 503, 'error' => 'Sub Stage Not Deleted']);
        }
        $sub_stage_arr->sub_stage_name = implode(',', $str_sub_stage);
        $sub_stage_arr->save();
        return response()->json(['code' => 200, 'success' => 'Sub Stage Deleted Successfully']);
    }
    public function updatepriority(PriorityReq $request)
    {
        if (!$this->user->can('stagemaster.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $new_priority = $request->new_priority;
        $old_priority = $request->old_priority;
        $stage_id = $request->stage_id;
        $data = StagemasterModel::where('id', $stage_id)->update(['priority' => $new_priority]);
        $data2 = StagemasterModel::where('priority', $new_priority)->where('id', '!=', $stage_id)->update(['priority' => $old_priority]);
        if($data)
        {
            return response()->json(['code' => 200, 'success' => 'Priority Updated Successfully']);
        }
        else
        {
            {
                return response()->json(['code' => 503, 'error' => 'Priority Not Updated Please Try Again']);
            }
        }
    }
    public function StageRenewal(Request $request)
    {
        if (!$this->user->can('stagemaster.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $subStages = $request->renewal_substage_val;
        $action = $request->action;
        $action = $action == 'remove' ? 'N' : 'Y';
        $renewalSubstage = substagemaster::whereIn('id',$subStages)->update(['is_renewal' => $action]);
        if($renewalSubstage)
        {
            return response()->json(['code' => 200, 'success' => 'Sub Stage Added For Renewal Successfully']);
        }
        else
        {
            return response()->json(['code' => 503, 'error' => 'Sub Stage Not Added For Renewal Please Try Again']);
        }
    }
    public function listStage(Request $request){
        $listStage = StagemasterModel::get();
        if(!empty($listStage)){
            return response()->json(['status' => 200, 'return_data' => $listStage, 'message' => 'Data Found']);
        }else{
            return response()->json(['status' => 500, 'return_data' => '',  'message' => 'No Data Found']);
        }
    }
}
