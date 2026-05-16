<?php

namespace App\Http\Controllers;

use App\Models\FuelType;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class FuelTypeController extends Controller
{
    public function create(Request $request){
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse; 
        }
        $rules=[
            'fuel_type' => 'required',];
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
            $fuel_type = new FuelType();
            $fuel_type->fuel_type = request()->fuel_type;
            $fuel_type->save();
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'fuel Type created successfully'
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
        $fuel_type_id = $request->id;
        $fuel_type = FuelType::findOrFail($fuel_type_id);   
        if($fuel_type){
            $fuel_type->update($request->all());
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'Fuel Type Updated Successfully',
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
        $fuel_type = FuelType::get();
        if($fuel_type->isEmpty()){
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Fuel Type  not found'
                ],
                500
            );
        }else{
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => $fuel_type,
                    'message' => 'Fuel Type List'
                ],
                200
            );
        }
        
    }
}
