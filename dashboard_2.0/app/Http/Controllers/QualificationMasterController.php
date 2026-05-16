<?php

namespace App\Http\Controllers;

use App\Models\QualificationMaster;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class QualificationMasterController extends Controller
{
    public function index(){
        $qualification = QualificationMaster::all();
        return view('qualification_master', compact('qualification'));
    }
    public function store(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $rules=[
            'qualification_name' => 'required',
        ];
        $validator = Validator::make(request()->all(),$rules);
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

            $qualification = new QualificationMaster();
            $qualification->qualification_name = request()->qualification_name;
            $qualification->save();
            if($qualification->save()){

                return response()->json(
                    [
                        'status' => 200,
                        'return_data' =>  $qualification,
                        'message' => 'qualification created successfully'
                    ],
                    200
                );
            }else{

                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Something went wrong'
                    ],
                    500
                );
            }
        }
    }

    public function update(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $qualification_master_id = $request->qualification_master_id;
        $qualification_type = QualificationMaster::findOrFail($qualification_master_id );

        $rules = [
            'qualification_name' => ['required', 'string'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Validation failed',
                    'errors' => $validator->errors(),
                ],
                500
            );
        }

        $faq = QualificationMaster::find($request->id);

        if (!$faq) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => $faq,
                    'message' => 'Qualification data not found',
                ],
                500
            );
        }



        $faq->qualification_name = $request->qualification_name;



        $faq->save();
        return response()->json(
            [
                'status' => 200,
                'return_data' => $faq,
                'message' => 'Qualification updated successfully',
            ],
            200
        );
    }
    public function QualificationList(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $qualification = QualificationMaster::get();
        if($qualification->isEmpty()){
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Qualification  not found'
                ],
                500
            );
        }else{
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => $qualification,
                    'message' => 'Qualification List'
                ],
                200
            );
        }

    }
    public function destroy(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $faq = QualificationMaster::where('qualification_master_id', $request->id)->first();

        if ($faq) {
            $faq->delete();
            return response()->json(['message' => 'Qualification deleted successfully']);
        } else {
            return response()->json(['message' => 'Qualification not found or already deleted']);
        }
    }


}
