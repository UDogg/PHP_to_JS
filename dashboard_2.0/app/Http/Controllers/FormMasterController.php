<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\FormBuilderMaster;
use App\Models\FormMaster;

class FormMasterController extends Controller
{
    public function index()
    {
        return view('form_master');
    }

    public function getItems()
    {

        $items = FormBuilderMaster::all();
        return response()->json($items);
    }
    public function show()
    {
        $submission = FormMaster::all();

        if (!$submission) {
            return response()->json(['message' => 'Submission not found'], 404);
        }

        return response()->json($submission);
    }

    public function submitForm(Request $request)
    {
        // $request->validate([
        //     'label_name' => 'required|string|max:255',
        //     'item_id' => 'required|exists:items,id',
        // ]);
        $item_value = FormBuilderMaster::find($request->item_id);
   
        if (!empty($request)) {

            FormMaster::create([
                'label_name' => $request->label_name,
                'item_id' => $request->item_id,
                'item_value' => $item_value['placeholder_name']?? '',
            ]);

            return ['status' => 200, 'success' => 'form Created Successfully'];
        } else {
            return ['status' => 503, 'error' => 'getting error'];
        }
    }

    public function edit($id)
    {
        $submission = FormMaster::find($id);
        $items = FormBuilderMaster::all();
        return view('form_master', compact('submission', 'items'));
    }

    public function update(Request $request, $id)
    {
        // $request->validate([
        //     'label_name' => 'required|string|max:255',
        //     'item_id' => 'required|exists:items,id',
        // ]);

        $submission = FormMaster::find($id);
        $submission->update([
            'label_name' => $request->label_name,
            'item_id' => $request->item_id,
        ]);

        return redirect()->route('form_master')->with('success', 'Data updated successfully!');
    }

    public function destroy($id)
    {
        $submission = FormMaster::find($id);
        $submission->delete();

        return redirect()->route('form_master')->with('success', 'Data deleted successfully!');
    }
}
