<?php

namespace App\Http\Controllers;

use App\Models\ChannelMaster;
use App\Models\BranchMaster;
use Illuminate\Http\Request;
use App\Models\cityMaster;
use Illuminate\Broadcasting\Channel;

class CityMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        //
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        $city_master = cityMaster::all();
        return view('city_master_store', compact('city_master'));
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $city_master = new cityMaster();        
        $city_master->city_name=$request->city_name;
        $city_master->save();
        if($city_master->save()){
            return redirect()->route('city_master.show')->with([
                'message' => 'City Added Successfully.'
            ]);
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        $city_master = cityMaster::all();
        return view('city_master_show', compact('city_master'));
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(string $id)
    {

        $city_master = cityMaster::findOrFail($id); 

        return view('city_master_edit', compact('city_master'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        $city_master = cityMaster::findOrFail($id);
        $city_master->update([
            'city_name' => $request->city_name
        ]);

        return redirect()->route('city_master_show.show')->with('message', 'City Updated Successfully.');
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $city_master = cityMaster::find($id);

        if (!$city_master) {
            return redirect()->route('city_master.index')
                ->with('error', 'City not found.');
        }

        $city_master->delete();
        return redirect()->route('city_master.show')
            ->with('message', 'City Deleted Successfully.');
    }
    public function channelMasterList()
    {
        $channels = ChannelMaster::select('channel_name')->get();
        $data = [];
        
        foreach ($channels as $channel) {
            $data[] = [
                'label' => $channel->channel_name,
                'value' => $channel->channel_name
            ];
        }

        return response()->json([
            'status' => 200,
            'return_data' => $data,
            'message' => 'Channel List',
        ]);
    }

    public function branchMasterList()
    {
        $branches = BranchMaster::select('branch_name')->get();
        $data = [];

        foreach ($branches as $branch) {
            $data[] = [
                'label' => $branch->branch_name,
                'value' => $branch->branch_name
            ];
        }

        return response()->json([
            'status' => 200,
            'return_data' => $data,
            'message' => 'Branch List',
        ]);
    }
}
