<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\PiFieldsModel;
use App\Models\MaskingType;

use Illuminate\Support\Facades\Schema;
use App\Models\MaskConfigurationMaster;
use Illuminate\Support\Facades\DB; 
use App\Models\RolePiDataMapping;
class MaskDataController extends Controller
{
    public function index()
    {
        $MaskData = PiFieldsModel::all();
        return view('MaskData.index', compact('MaskData'));
    }

    public function create()
    {
        return view('MaskData.create');
    }

    public function store(Request $request)
    {
        $request->validate([
            'field_name' => 'required',
            'status' => 'nullable'
        ]);

        PiFieldsModel::create($request->all());

        return redirect()->route('MaskData.index')->with('success', 'Created Successfully');
    }

    public function show($id)
    {
        $data = PiFieldsModel::findOrFail($id);
        return view('MaskData.show', compact('data'));
    }

    public function edit($id)
    {
        $data = PiFieldsModel::findOrFail($id);
        return view('MaskData.edit', compact('data'));
    }

    public function update(Request $request, $id)
    {
        $request->validate([
            'field_name' => 'required'
        ]);

        $data = PiFieldsModel::findOrFail($id);
        $data->update($request->all());

        return redirect()->route('MaskData.index')->with('success', 'Updated Successfully');
    }

    public function destroy($id)
    {
        $data = PiFieldsModel::findOrFail($id);
        $data->delete();

        return redirect()->route('MaskData.index')->with('success', 'Deleted Successfully');
    }
    
    public function getPiFields()
    {
        $piFields = PiFieldsModel::where('status', 'Y')->select('field_name')->get();
        $data = [];

        foreach ($piFields as $fields) {
            $data[] = [
                'label' => $fields->field_name,
                'value' => $fields->field_name
            ];
        }

        return response()->json([
            'status' => 200,
            'return_data' => $data,
            'message' => 'PI Fields retrieved successfully'
        ]);
    }

    public function maskingTypeList()
    {

        $maskType = MaskingType::select('mask_name','mongo_key')->get();
        $data = [];
        foreach ($maskType as $type) {
            $data[] = [
                'label' => $type->mask_name,
                'value' => $type->mongo_key
            ];
        }
        return response()->json([
            'return_data' => $data,
            'status' => 200,
            'message' => 'Masking types retrieved successfully'
        ]);
    }

    public function storeMaskingType(Request $request)
    {
        $request->validate([
            'mask_name' => 'required|string',
            'mongo_key' => 'required|string'
        ]);

        $data = MaskingType::create([
            'mask_name' => $request->mask_name,
            'mongo_key' => $request->mongo_key
        ]);

        return response()->json([
            'return_data' => $data,
            'status' => 200,
            'message' => 'Created successfully',
        ]);
    }


    public function updateMaskingType(Request $request)
    {
        $data = MaskingType::find($request->id);

        if (!$data) {
            return response()->json([
                'status' => 500,
                'message' => 'Not found'
            ], 404);
        }

        $data->update([
            'mask_name' => $request->mask_name
        ]);

        return response()->json([
            'status' => 200,
            'message' => 'Updated successfully',
            'data' => $data
        ]);
    }

    public function deleteMaskingType(Request $request)
    {
        $data = MaskingType::find($request->id);

        if (!$data) {
            return response()->json([
                'status' => 500,
                'message' => 'Not found'
            ], 404);
        }

        $data->delete();

        return response()->json([
            'status' => 200,
            'message' => 'Deleted successfully'
        ]);
    }

    public function maskingConfigurator(Request $request)
    {
        $module     = $request->module;
        $role       = $request->role;
        $usertype   = $request->usertype;
        $fields     = $request->fields;

        $existing = MaskConfigurationMaster::where([
            'module_name' => $module,
            'role'        => $role,
            'usertype'    => $usertype,
        ])->first();

        if ($existing) {
            RolePiDataMapping::where('module_id', $existing->id)->delete();
            $existing->delete();
        }

        $master = MaskConfigurationMaster::create([
            'module_name' => $module,
            'role'        => $role,
            'usertype'    => $usertype,
        ]);

        $insertData = [];

        foreach ($fields as $field) {
            $insertData[] = [
                'module_id'   => $master->id,
                'field_name'  => $field['field_key'],
                'is_enabled'  => $field['enabled'] ?? 'Y',
                'mask_type'   => $field['mask_type'] ?? null,
                'mask_scope'  => $field['masking_scope'] ?? null,
                'mask_formula'=> $field['mask_formula'],
                'created_at'  => now(),
                'updated_at'  => now(),
            ];
        }
        RolePiDataMapping::insert($insertData);

        return response()->json([
            'return_data' => $insertData,
            'status' => 200,
            'message' => 'Masking configuration saved successfully'
        ]);
    }
    
    public function maskConfigurationMasterList(Request $request)
    {
        $perPage = $request->input('per_page', 10); 

        $configurations = MaskConfigurationMaster::select(
                'module_name',
                'role',
                'usertype',
                'status'
            )
            ->paginate($perPage);

        return response()->json([
            'return_data' => $configurations->items(),
            'pagination' => [
                'current_page' => $configurations->currentPage(),
                'last_page'    => $configurations->lastPage(),
                'per_page'     => $configurations->perPage(),
                'total'        => $configurations->total(),
            ],
            'status' => 200,
            'message' => 'Masking configuration master list retrieved successfully'
        ]);
    }

    public function editmaskingConfigurator(Request $request)
    {
        $module   = $request->module;
        $role     = $request->role;
        $usertype = $request->usertype;

        $moduleData = DB::table('mask_configuration_master')
            ->where('module_name', $module)
            ->where('role', $role)
            ->where('usertype', $usertype)
            ->where('status', 'Y')
            ->orderByDesc('id')
            ->first();

        if ($moduleData) {
            $mappingData = DB::table('role_pi_data_mapping')
                ->where('module_id', $moduleData->id)
                ->get();

            return response()->json([
                'status'  => true,
                'data'    => $mappingData,
                'message' => 'Filtered data fetched successfully'
            ]);
        }

        $columns = Schema::getColumnListing('role_pi_data_mapping');

        $fields = DB::table('pi_fields_master')
            ->where('status', 'Y')
            ->pluck('field_name'); 

        $data = [];

        foreach ($fields as $field) {
            $row = [];

            foreach ($columns as $column) {

            if ($column == 'id') continue;

            if ($column == 'field_name') {
                $row[$column] = $field;
            } elseif ($column == 'is_enabled') {
                $row[$column] = "Y"; 
            } else {
                $row[$column] = "";
            }
        }

            $data[] = $row;
        }

        return response()->json([
            'status'  => true,
            'data'    => $data,
            'message' => 'Data not found'
        ]);
    }

}
