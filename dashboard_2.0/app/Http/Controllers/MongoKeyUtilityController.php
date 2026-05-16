<?php

namespace App\Http\Controllers;

use App\Models\lobMaster;
use App\Models\PolicyStatusColumnMaster;
use Illuminate\Http\Request;

class MongoKeyUtilityController extends Controller
{
    public function index()
    {
        $policy_status_columns = PolicyStatusColumnMaster::latest()->paginate(10);
        return view('mongo_key_Utility', compact('policy_status_columns'));
    }

    public function store(Request $request)
    {
        $data = $request->validate([
            'column_name' => 'required',
            'is_default' => 'required',
            'is_visible' => 'required',
        ]);

        $lobs = lobMaster::where('is_enabled','Y')->pluck('id')->toArray();

        $existsingLobs = PolicyStatusColumnMaster::whereIn('lob', $lobs)
            ->where('column_name', $data['column_name'])
            ->pluck('lob')
            ->toArray();

        foreach ($lobs as $lob_id) {
            if(in_array($lob_id, $existsingLobs)){
                continue; 
            }
            $data['lob'] = $lob_id;
            PolicyStatusColumnMaster::create($data);
        }

        return response()->json(['success' => true]);
    }

    public function show($id)
    {
        return response()->json([
            'data' => PolicyStatusColumnMaster::findOrFail($id)
        ]);
    }

    public function update(Request $request, $id)
    {
        $record = PolicyStatusColumnMaster::findOrFail($id);

        $record->update($request->all());

        return response()->json(['success' => true]);
    }

    public function destroy($id)
    {
        PolicyStatusColumnMaster::findOrFail($id)->delete();

        return response()->json(['success' => true]);
    }
}