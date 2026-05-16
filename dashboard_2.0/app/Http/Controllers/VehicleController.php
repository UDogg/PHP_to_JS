<?php

namespace App\Http\Controllers;

use App\Models\VehicleModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class VehicleController extends Controller
{
    public function create(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $rules=[
            'name'=>'required'
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
        }
        else{
            $vehicle = new VehicleModel();
            $vehicle->name = request()->name;
            $vehicle->save();
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'vehicle created successfully'
                ],
                200
            );
        }
    }
    public function update(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $vehicle_id = $request->id;
        $vehicle = VehicleModel::findOrFail($vehicle_id);   
        if($vehicle){
            $vehicle->update($request->all());
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'Status Updated Successfully',
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
    public function VehicleList(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $vehicle = VehicleModel::get();
        if($vehicle->isEmpty()){
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'vehicle not found'
                ],
                500
            );
        }else{
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => $vehicle,
                    'message' => 'Vehicle List'
                ],
                200
            );
        }
        
    }
}
