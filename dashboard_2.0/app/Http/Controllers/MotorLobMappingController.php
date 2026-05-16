<?php

namespace App\Http\Controllers;

use App\Models\lobMaster;
use Illuminate\Support\Str;
use Illuminate\Http\Request;
use App\Models\MotorLobMappingModel;

class MotorLobMappingController extends Controller
{
    public function index(Request $request)
    {
        $query = MotorLobMappingModel::query();

        if ($request->has('search')) {
           $search = $request->input('search');
           $query->where(function ($q) use ($search) {
             $q->where('lob', 'like', "%{$search}%")
                ->orWhere('motor_lob', 'like', "%{$search}%")
                ->orWhere('report_ob', 'like', "%{$search}%");
            });
        }

        if ($request->has('start_date')) {
          $query->whereDate('created_at', '>=', $request->input('start_date'));
        }

        if ($request->has('end_date')) {
          $query->whereDate('created_at', '<=', $request->input('end_date'));
       }

        $perPage = $request->input('per_page', 10);
        $mappings = $query->orderBy('id', 'desc')->paginate($perPage);

        if ($request->expectsJson()) {
            return response()->json([
               'message' => 'Motor LOB Mappings retrieved successfully.',
               'data' => $mappings->items(),
               'pagination' => [
                   'total' => $mappings->total(),
                   'per_page' => $mappings->perPage(),
                   'current_page' => $mappings->currentPage(),
                   'last_page' => $mappings->lastPage(),
                ],
           ]);
       }

        if (MotorLobMappingModel::count() === 0) {
            if ($request->expectsJson()) {
                    return response()->json([
                        'message' => 'No data found in the Motor LOB Mappings table.',
                        'data' => [],
                        'pagination' => null,
                    ]);
                }

                $columns = ['LOB', 'Motor Lob', 'Report Ob', 'Is Active', 'Created At', 'Updated At'];
                return view('MotorLobMapping.index', compact('columns', 'mappings'));
        }

        if ($mappings->count() > 0) {
            $columns = array_keys($mappings->first()->toArray());
        } else {
            $columns = ['lob', 'motor_lob', 'report_ob', 'is_active', 'created_at', 'updated_at'];
       }

        foreach ($columns as $key => $value) {
          if ($value === 'id') {
            unset($columns[$key]);
          } else {
            $columns[$key] = Str::title(str_replace('_', ' ', $value));
          }
       }

       return view('MotorLobMapping.index', compact('columns', 'mappings'));
    }



  
    public function create()
    {
        $loblist = lobMaster::select('lob','id')->get();
        return view('MotorLobMapping.create')->with('loblist', $loblist);
    }


    public function store(Request $request)
    {
        $validated = $request->validate([
            'lob' => 'required|string|max:255',
            'motor_lob' => 'required|string|max:255',
            'report_ob' => 'required|string|max:255',
            'is_active' => 'sometimes',
        ]);
    
        $mapping = MotorLobMappingModel::create($validated);

        if ($request->expectsJson()) {
            return response()->json([
                'message' => 'Motor LOB Mapping created successfully.',
                'data' => $mapping
            ], 201);
        }
    
        return redirect()->route('motorLobMapping.index')
            ->with([
                'class' => 'success',
                'message' => 'Motor LOB Mapping created successfully.'
        ]);
    }

    public function edit(string $id)
    {
        $mapping = MotorLobMappingModel::findOrFail($id);
        $loblist = lobMaster::select('lob','id')->get();
        return view('MotorLobMapping.edit', compact('mapping', 'loblist'));
    }
    

    public function update(Request $request, string $id)
    {
        $validated = $request->validate([
           'lob' => 'required|string|max:255',
           'motor_lob' => 'required|string|max:255',
           'report_ob' => 'required|string|max:255',
           'is_active' => 'sometimes',  
        ]);

         $mapping = MotorLobMappingModel::findOrFail($id);

        $mapping->update($validated);

        if ($request->expectsJson()) {
            return response()->json([
                'message' => 'Motor LOB Mapping updated successfully.',
                'data' => $mapping
            ], 200);
        }

        return redirect()->route('motorLobMapping.index')
        ->with([
            'class' => 'success',
            'message' => 'Motor LOB Mapping updated successfully.'
        ]);
   }



   public function destroy(Request $request, string $id)
   {
       $mapping = MotorLobMappingModel::findOrFail($id);
       $mapping->delete();

        if ($request->expectsJson()) {
            return response()->json([
               'message' => 'Motor LOB Mapping deleted successfully.'
            ], 200);
        }

        return redirect()->route('motorLobMapping.index')
        ->with([
            'class' => 'success',
            'message' => 'Motor LOB Mapping deleted successfully.'
        ]);
    }
}
