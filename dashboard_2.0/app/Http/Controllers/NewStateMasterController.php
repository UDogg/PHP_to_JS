<?php

namespace App\Http\Controllers;

use App\Models\stateMaster;
use Illuminate\Http\Request;

class NewStateMasterController extends Controller
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
        $state_master = stateMaster::all();
        return view('state_master_store', compact('state_master'));
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $state_master = new stateMaster();
        $state_master->state_name = $request->state_name;
        $state_master->save();
        if ($state_master->save()) {
            return redirect()->route('state_master.show')->with([
                'message' => 'State Added Successfully.'
            ]);
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        $state_master = stateMaster::all();
        return view('state_master_show', compact('state_master'));
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(string $id)
    {

        $state_master = stateMaster::findOrFail($id);

        return view('state_master_edit', compact('state_master'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        $state_master = stateMaster::findOrFail($id);
        $state_master->update([
            'state_name' => $request->state_name
        ]);

        return redirect()->route('state_master.show')->with('message', 'State Updated Successfully.');
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $state_master = stateMaster::find($id);

        if (!$state_master) {
            return redirect()->route('state_master.index')
                ->with('error', 'State not found.');
        }

        $state_master->delete();
        return redirect()->route('state_master.show')
            ->with('message', 'State Deleted Successfully.');
    }
}
