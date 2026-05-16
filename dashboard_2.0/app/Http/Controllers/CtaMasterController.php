<?php

namespace App\Http\Controllers;

use App\Models\CtaMasterModel;
use App\Models\lobMaster;
use App\Models\PolicyStatusColumnMaster;
use App\Models\StagemasterModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class CtaMasterController extends Controller
{

    public function index(Request $request)
    {
        $lobFilter = $request->get('lob');
        $lobMasterData = lobMaster::select('id', 'lob_name', 'lob')->where('is_enabled', 'Y')->get();
        $stageMasterData = StagemasterModel::select('id', 'stage_name')->get();
        $ctaName = PolicyStatusColumnMaster::select('id', 'column_name')->get();

        $ctaQuery = CtaMasterModel::join('stage_master as b', 'cta_master.stage', '=', 'b.id')
            ->join('lob_master as c', 'cta_master.lob', '=', 'c.id')
            ->join('policystatus_column_master', 'cta_master.cta_name', '=', 'policystatus_column_master.column_name')
            ->select('cta_master.*', 'c.lob as lob', 'b.stage_name as stage', 'b.id as stage_id', 'c.id as lob_id',
                    'policystatus_column_master.column_name as cta_name');

        if ($lobFilter) {
            $ctaQuery->where('c.lob', $lobFilter);
        }

        $cta = $ctaQuery->distinct()->get();

        return view('cta_master', compact('lobMasterData', 'stageMasterData', 'ctaName', 'cta'));
    }


    public function store(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $rules = [
            'lobMasterData' => ['required'],
            'stageMasterData' => ['required'],
            'ctaName' => ['required'],
            'redirection_url' => ['nullable', 'string'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => $validator->errors(),
                    'message' => 'Invalid request data',
                ],
                500
            );
        } else {
            if (!empty(($request->lobMasterData) && ($request->stageMasterData))) {
                $data = CtaMasterModel::where('lob', $request->lobMasterData)->where('stage', $request->stageMasterData)->first();
                if (!empty($data)) {
                    return response()->json([
                        'status' => 500,
                        'message' => 'CTA already exists',
                    ]);

                }
            }
            $cta = new CtaMasterModel();
            $cta->lob = $request->lobMasterData;
            $cta->stage = $request->stageMasterData;
            $cta->cta_name = $request->ctaName;
            $cta->redirection_url = $request->redirection_url ?: null;

            if ($cta->save()) {
                $cta_lob_name = lobMaster::where('id', $request->lobMasterData)->first();
                $cta -> lob_name = $cta_lob_name->lob;
                $cta_stage_name = StagemasterModel::where('id', $request->stageMasterData)->first();
                $cta -> stage_name = $cta_stage_name->stage_name;

                $cta->save();

                return response()->json([
                    'status' => 200,
                    'return_data' => $cta,
                    'message' => 'CTA Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Failed to save CTA',
                    ],
                    500
                );
            }
        }
    }

    public function destroy(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $cta = CtaMasterModel::where('id', $request->id)->first();

        if ($cta) {
            $cta->delete();
            return response()->json([
                'message' => 'CTA Data deleted successfully',
            ], 200);
        } else {
            return response()->json([
                'message' => 'CTA Data not found or already deleted',
            ], 404);
        }
    }
    public function update(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $cta = CtaMasterModel::find($request->id);

        if ($cta) {
            $cta->lob = $request->Lob;
            $cta->stage = $request->stage;
            $cta->cta_name = $request->cta;
            $cta->redirection_url = $request->redirectionUrl;

            if ($cta->save()) {
                return response()->json([
                    'message' => 'CTA updated successfully',
                ], 200);
            } else {
                return response()->json([
                    'message' => 'Failed to update CTA',
                ], 500);
            }
        } else {
            return response()->json([
                'message' => 'CTA not found',
            ], 404);
        }
    }
    public function show(Request $request)
    {

        $lobFilter = $request->get('lob');
        $ctaQuery = CtaMasterModel::join('stage_master as b', 'cta_master.stage', '=', 'b.id')
            ->join('lob_master as c', 'cta_master.lob', '=', 'c.id')
            ->join('policystatus_column_master', 'cta_master.cta_name', '=', 'policystatus_column_master.column_name')
            ->select('cta_master.*', 'c.lob as lob', 'b.stage_name as stage',
                    'policystatus_column_master.column_name as cta_name');
        if ($lobFilter) {
            $ctaQuery->where('c.lob', $lobFilter);
        }
        $cta = $ctaQuery->distinct()->get();
        return response()->json([
            'status' => 200,
            'cta' => $cta,
        ]);
    }

}
