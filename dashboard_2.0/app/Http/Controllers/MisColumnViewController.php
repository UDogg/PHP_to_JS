<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\MisColumnView;
use App\Models\GroupingReportKeyUtility;

class MisColumnViewController extends Controller
{
    public function index()
    {
        $items = MisColumnView::all();
        return view('mis_column_view', compact('items'));
    }

    public function getMongoKeys()
    {
        $templateList = GroupingReportKeyUtility::join('key_utility', 'key_utility.id', '=', 'key_utility_report.key_utility_id')
            ->leftJoin('key_utility_mapping', 'key_utility_mapping.key_id', '=', 'key_utility.id')
            ->leftJoin('policystatus_column_master', 'policystatus_column_master.id', '=', 'key_utility_mapping.mapping_id')
            ->select('key_utility_report.key', 'policystatus_column_master.column_name')
            ->get();
    
        if ($templateList->isEmpty()) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Data Not found',
            ]);
        }
    
        $groupedData = $templateList->groupBy('key')->map(function ($items, $key) {
            return [
                "key" => $key,
                "column_names" => array_values($items->pluck('column_name')->unique()->toArray())
            ];
        })->values();
    
        return response()->json([
            'status' => 200,
            'return_data' => $groupedData->toArray(),
            'message' => 'Data Fetched successfully',
        ]);
    }



    public function store(Request $request)
    {
        MisColumnView::create([
            'mongo_key' => $request->mongo_key,
            'existing_value' => $request->existing_value,
            'new_value' => $request->new_value,
        ]);

        return redirect()->route('miscolumnview.index');
    }

    public function update(Request $request, $id)
    {
        MisColumnView::where('id', $id)->update([
            'mongo_key' => $request->mongo_key,
            'existing_value' => $request->existing_value,
            'new_value' => $request->new_value,
        ]);

        return redirect()->route('miscolumnview.index');
    }

    public function delete($id)
    {
        MisColumnView::where('id', $id)->delete();
        return redirect()->route('miscolumnview.index');
    }
}
