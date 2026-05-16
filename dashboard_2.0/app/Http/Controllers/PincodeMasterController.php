<?php

namespace App\Http\Controllers;

use App\Models\cityMaster;
use App\Models\pincodeMaster;
use App\Models\stateMaster;
use Illuminate\Http\Request;

class PincodeMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        $pincode_master = pincodeMaster::all();
        $city_master = cityMaster::all();
        $state_master = stateMaster::all();
        return view('pincode_master_store', compact('pincode_master', 'city_master', 'state_master'));
    }

    /**
     * Store a newly created resource in storage.
     */

    public function store(Request $request)
    {
        $pincode = pincodeMaster::create(
            $request->except('area', 'latitude', 'longitude', 'geospatial_accuracy', 'sequence', 'created_at', 'updated_at', 'deleted_at')
        );

        if ($request->wantsJson()) {
            return response()->json([
                'status' => 200,
                'return_data' => $pincode,
                'message' => 'Pincode created successfully!',
            ]);
        }

        return redirect()->route('pincode_master.show', $pincode)
            ->with(['message' => 'Pincode created successfully!']);
    }


    /**
     * Display the specified resource.
     */
    public function show()
    {
        $pincode = pincodeMaster::leftJoin('city_masters', 'pincode_masters.city_id', '=', 'city_masters.city_id')
            ->leftJoin('state_masters', 'pincode_masters.state_id', '=', 'state_masters.state_id')
            ->select(
                'pincode_masters.*',
                'state_masters.state_name as state',
                'city_masters.city_name as city'
            )
            ->get();
        return view('pincode_master_show', compact('pincode'));
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(string $id)
    {
        $pincode_master = pincodeMaster::findOrFail($id); 
        $city_master = cityMaster::select('city_id', 'city_name')->get();
        $state_master = stateMaster::select('state_id', 'state_name')->get();

        return view('pincode_master_edit', compact('city_master', 'state_master', 'pincode_master'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        $pincode_master = pincodeMaster::findOrFail($id);
        $pin = pincodeMaster::leftJoin('city_masters', 'pincode_masters.pincode_id', '=', 'city_masters.city_id')
            ->leftJoin('state_masters', 'pincode_masters.pincode_id', '=', 'state_masters.state_id')
            ->select(
                'pincode_masters.*',
                'state_name as state',
                'city_name as city'
            )
            ->get();
        $pincode_master->update([
            'pincode' => $request->pincode,
            'country_code' => $request->country_code,
            'state_id' => $request->state_id,
            'city_id' => $request->city_id,
        ]);

        return redirect()->route('pincode_master.show.show')->with('message', 'Column Updated Successfully.');
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $pincode_master = pincodeMaster::find($id);

        if (!$pincode_master) {
            return redirect()->route('pincode_master.index')
                ->with('error', 'Pincode not found.');
        }

        $pincode_master->delete();
        return redirect()->route('pincode_master.show')
            ->with('message', 'Pincode Deleted Successfully.');
    }

    public function getPincodeDetails(Request $request)
    {
        $pincode = $request->input('pincode'); 

        if (!$pincode) {
            return response()->json([
                'status' => 400,
                'message' => 'Pincode ID is required'
            ], 400);
        }

        $pin = pincodeMaster::where('pincode', $pincode)
        ->leftJoin('city_masters', 'pincode_masters.city_id', '=', 'city_masters.city_id')
        ->leftJoin('state_masters', 'pincode_masters.state_id', '=', 'state_masters.state_id')
        ->select(
                'pincode_masters.*',
                'city_masters.city_name',
                'state_masters.state_name'
            )
            ->first();

        if (!$pin) {
            return response()->json([
                'status' => 404,
                'message' => 'Pincode not found'
            ], 404);
        } 

        return response()->json([
            'status' => 200,
            'return_data' => $pin,
            'message' => 'Pincode found successfully'
        ], 200);
    }
}
