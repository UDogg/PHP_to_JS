<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\ExcelKeyMaster;
use App\Models\PolicyStatusColumnMaster;
use Maatwebsite\Excel\Facades\Excel;

class ExcelKeyColumnController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        $column = PolicyStatusColumnMaster::join('excel_key_master', 'policystatus_column_master.id', '=', 'excel_key_master.policystatus_column_master_id')
        ->select('excel_key_master.*', 'policystatus_column_master.column_name as policy_status_name')
        ->get();

        return view('index_excel_key_column',compact('column'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create(Request $request)
    {
        $policyStatus = PolicyStatusColumnMaster::all();
        return view('excel_key_column',compact('policyStatus'));
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $policyStatus = PolicyStatusColumnMaster::all();
        $column = new ExcelKeyMaster();        
        $column->policystatus_column_master_id=$request->policystatus_column_master_id;
        $column->excel_column_name=$request->excel_column_name;
        $column->sequence=$request->sequence;
        $column->lob_id=$request->lob_id;
        $column->is_visible=$request->is_visible;
        $column->save();
        if($column->save()){
            return redirect()->route('excel_column.index')->with([
                'message' => 'Column Added Successfully.'
            ]);
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        
        $column = PolicyStatusColumnMaster::join('excel_key_master', 'policystatus_column_master.id', '=', 'excel_key_master.policystatus_column_master_id')
        ->select('excel_key_master.*', 'policystatus_column_master.column_name as policy_status_name')
        ->get();

        return view('index_excel_key_column',compact('column'));
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(string $id)
    {
        $column = ExcelKeyMaster::findOrFail($id); // Retrieve the record being edited
        $policyStatus = PolicyStatusColumnMaster::select('id', 'column_name')->get(); // Retrieve dropdown options

        return view('edit_excel_key_column', compact('column', 'policyStatus'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, $id)
    {
        $column = ExcelKeyMaster::findOrFail($id);
        $policyStatus = PolicyStatusColumnMaster::join('excel_key_master', 'policystatus_column_master.id', '=', 'excel_key_master.policystatus_column_master_id')
        ->select('excel_key_master.*', 'policystatus_column_master.column_name as policy_status_name')
        ->get();
        $column->update([
            'policystatus_column_master_id' => $request->policystatus_column_master_id,
            'excel_column_name' => $request->excel_column_name,
            'sequence' => $request->sequence,
            'lob_id' => $request->lob_id,
            'is_visible' => $request->is_visible,
        ]);
    
        return redirect()->route('excel_column.index')->with('message', 'Column Updated Successfully.');
    }
    

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $column = ExcelKeyMaster::find($id);
        $column->delete();
        return redirect()->route('excel_column.index')->with('message', 'Column Deleted Successfully.');

    }

   public function add_column(Request $request)
    {
        $request->validate([
            'ColumnName' => 'required|string|max:255',
        ]);
    
        $data = [
            'column_name' => $request->ColumnName,
            'alias' => $request->ColumnNameAlias,
            'is_default' => $request->isDefault ?? "N",
            'is_visible' => $request->isVisible ?? "N",
            'lob' => !empty($request->selectlob) ? implode(',', $request->selectlob) : null,
            'stage' => !empty($request->selectStage) ? implode(',', $request->selectStage) : null,
        ]; 
    
        PolicyStatusColumnMaster::create($data);
    
        return redirect()->back()->with('success', 'Column added successfully.');
    }
}
