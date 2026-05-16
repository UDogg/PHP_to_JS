<?php

namespace App\Http\Controllers;

use App\Models\RoleCodeMapping;
use Illuminate\Http\Request;

class RoleCodeMappingController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        $data = RoleCodeMapping::all();

        return response()->json([
            'success' => true,
            'data' => $data,
        ],200);
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        try {
            $validated = $request->validate([
                'role_id'         => 'required|integer',
                'parameter_name'  => 'required|string',
                'parameter_value' => 'required|string',
                'status'          => 'required|in:0,1',
            ]);

            $exists = RoleCodeMapping::where('role_id', $request->role_id)
                ->where('parameter_name', $request->parameter_name)
                ->where('parameter_value', $request->parameter_value)
                ->exists();

            if ($exists) {
                return response()->json([
                    'success' => false,
                    'message' => 'This role and parameter name already exists.'
                ], 422);
            }

            $record = RoleCodeMapping::create($validated);

            return response()->json([
                'success' => true,
                'message' => 'Record created successfully.',
                'data'    => $record,
            ], 200);
        } catch (\Exception $e) {
            return response()->json([
                'success' => false,
                'message' => 'Something went wrong while creating the record.',
                'error'   => $e->getMessage(), // You can hide this in production
            ], 500);
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        $record = RoleCodeMapping::find($id);

        if (!$record) {
            return response()->json([
                'success' => false,
                'message' => 'Record not found.',
            ], 404);
        }

        return response()->json([
            'success' => true,
            'data'    => $record,
        ],200);
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        try {
            $record = RoleCodeMapping::find($id);

            if (!$record) {
                return response()->json(['success' => false, 'message' => 'Record not found.'], 404);
            }

            $validated = $request->validate([
                'role_id'         => 'sometimes|integer',
                'parameter_name'  => 'sometimes|string',
                'parameter_value' => 'sometimes|string',
                'status'          => 'sometimes|in:0,1',
            ]);

            $exists = RoleCodeMapping::where('role_id', $request->role_id)
                ->where('parameter_name', $request->parameter_name)
                ->where('id', '!=', $id)
                ->exists();

            if ($exists) {
                return response()->json([
                    'success' => false,
                    'message' => 'This role and parameter name already exists.'
                ], 422);
            }

            $record->update($validated);

            return response()->json([
                'success' => true,
                'message' => 'Record updated successfully.',
                'data'    => $record,
            ],200);
        } catch (\Exception $e) {
            return response()->json([
                'success' => false,
                'message' => 'Something went wrong while updating the record.',
                'error'   => $e->getMessage(),
            ], 500);
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        try {
            $record = RoleCodeMapping::find($id);

            if (!$record) {
                return response()->json(['success' => false, 'message' => 'Record not found.'], 404);
            }

            $record->delete();

            return response()->json(['success' => true, 'message' => 'Record deleted successfully.'],200);
        } catch (\Exception $e) {
            return response()->json([
                'success' => false,
                'message' => 'Something went wrong while deleting the record.',
                'error'   => $e->getMessage(),
            ], 500);
        }
    }

     public function getDatabyRoleId(Request $request){

         $record = RoleCodeMapping::where('role_id',$request->role_id)->get();

        if (empty($record)) {
            return response()->json([
                'success' => false,
                'message' => 'Record not found.',
            ], 404);
        }

        return response()->json([
            'success' => true,
            'data'    => $record,
        ],200);
    }

    public function delete(Request $request)
    {
        try {
            $record = RoleCodeMapping::find($request->id);

            if (!$record) {
                return response()->json(['success' => false, 'message' => 'Record not found.'], 404);
            }

            $record->delete();

            return response()->json(['success' => true, 'message' => 'Record deleted successfully.'],200);
        } catch (\Exception $e) {
            return response()->json([
                'success' => false,
                'message' => 'Something went wrong while deleting the record.',
                'error'   => $e->getMessage(),
            ], 500);
        }
    }


}
