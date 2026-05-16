<?php

namespace App\Http\Controllers;

use App\Models\lobMaster;
use App\Models\Section;
use App\Models\SectionField;
use App\Models\ServiceSupportType;
use App\Models\StatusMaster;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class StatusMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index(Request $request)
    {

        $sst = ServiceSupportType::all();
        $section = Section::all();

        $paginate = $request->paginate ?? 10;
        $search_val = $request->search_val;

        $Query = StatusMaster::select('status_id', 'status_name', 'created_at');
        $count = $Query->count();
        $AllStatus = $Query->paginate($paginate)->all();

        $QuerySst = ServiceSupportType::select('sst_id', 'service_support_type', 'created_at');
        $countSst = $QuerySst->count();
        $AllSst = $QuerySst->paginate($paginate)->all();

        $QuerySection = Section::select('section_id', 'lob', 'service_support_type', 'section_name', 'created_at');
        $countSection = $QuerySection->count();
        $AllSection = $QuerySection->paginate($paginate)->all();

        $QueryField = SectionField::select('field_id', 'lob', 'service_support_type', 'section_name', 'section_field_name', 'created_at');
        $countField = $QueryField->count();
        $AllField = $QueryField->paginate($paginate)->all();

        $fetchLob = lobMaster::select('lob_name')->where('is_enabled', 'Y')->get();
        return view('endorsement.service_support', compact('count', 'AllStatus', 'countSst', 'AllSst', 'countSection', 'AllSection', 'countField', 'AllField',  'sst', 'section', 'fetchLob'));

    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $rules = [
            'status_name' => 'sometimes|required|string|max:255',
            'service_support_type' => 'sometimes|required|string|max:255', // Validation rule for service_support_type
        ];

        // Validate request data
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'validations fails',
                    'errors' => $validator->errors(),
                ],
                500
            );
        } else {
            // Check if 'status_name' exists in the request
            if ($request->has('status_name')) {
                $status_name = StatusMaster::create($request->only('status_name'));
                if ($status_name) {
                    return response()->json([
                        'status' => "200",
                        'return_data' => [],
                        'message' => 'Status Created Successfully',
                    ], 200);
                } else {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'Status not created',
                        ],
                        500
                    );
                }
            } elseif ($request->has('service_support_type')) { // Check if 'service_support_type' exists in the request
                $service_support_type = ServiceSupportType::create($request->only('service_support_type'));
                if ($service_support_type) {
                    return response()->json([
                        'status' => "200",
                        'return_data' => [],
                        'message' => 'Service Support Type Created Successfully',
                    ], 200);
                } else {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'Service Support Type not created',
                        ],
                        500
                    );
                }
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }

    }
    // store section
    public function storeSection(Request $request)
    {

        $rules = [
            'lob' => ['required', 'string'], // Validate as integer and ensure it's positive
            'service_support_type' => ['required', 'string'], // Adjust as per your actual requirements
            'section_name' => ['required'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        } else {
            $AllSection = new Section();
            $AllSection->lob = $request->lob; // Store total minutes in the database
            $AllSection->service_support_type = $request->service_support_type;
            $AllSection->section_name = $request->section_name;
            $AllSection->save();

            if ($AllSection->save()) {
                return response()->json([
                    'status' => "200",
                    'return_data' => [],
                    'message' => 'Service Support Type Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }
    }

    // store section
    public function storeField(Request $request)
    {
        $rules = [
            'lob' => ['required', 'string'], // Validate as integer and ensure it's positive
            'service_support_type' => ['required', 'string'], // Adjust as per your actual requirements
            'section_name' => ['required'],
            'section_field_name' => ['required'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        } else {
            $AllField = new SectionField();
            $AllField->lob = $request->lob; // Store total minutes in the database
            $AllField->service_support_type = $request->service_support_type;
            $AllField->section_name = $request->section_name;
            $AllField->section_field_name = $request->section_field_name;
            $AllField->save();

            if ($AllField->save()) {
                return response()->json([
                    'status' => "200",
                    'return_data' => [],
                    'message' => 'Field Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        //
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request)
    {

        $rules = [
            'status_name' => 'required|string|max:255',
        ];
        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Validation fails',
                    'errors' => $validator->errors(),
                ],
                500
            );
        } else {

            $status = StatusMaster::findOrFail($request->id);
            if ($status) {
                $status->update($request->all());

                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => 'Status Updated Successfully',
                    ],
                    200
                );
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Status not found',
                    ],
                    500
                );
            }
        }
    }

    public function updateSst(Request $request)
    {
        // dd($request->all());

        $rules = [
            'service_support_type' => 'required|string|max:255',
        ];
        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Validation fails',
                    'errors' => $validator->errors(),
                ],
                500
            );
        } else {

            $AllSst = ServiceSupportType::findOrFail($request->id);
            if ($AllSst) {
                $AllSst->update($request->all());

                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => 'Status Updated Successfully',
                    ],
                    200
                );
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Status not found',
                    ],
                    500
                );
            }
        }
    }

    public function updateSection(Request $request)
    {
        $rules = [
            'lob' => 'required|string|max:255',
            'section' => 'required|string|max:255',
            'sst' => 'required|string|max:255',
            'id' => 'required|string|max:255',
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Validation fails',
                    'errors' => $validator->errors(),
                ],
                500
            );
        } else {
            $AllField = Section::find($request->id);
            if ($AllField) {
                $AllField->update([
                    'lob' => $request->lob,
                    'section_name' => $request->section,
                    'service_support_type' => $request->sst,
                ]);

                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => 'Section Updated Successfully',
                    ],
                    200
                );
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Section not found',
                    ],
                    500
                );
            }
        }
    }

    // update section
    // public function updateField(Request $request)
    // {

    //     $rules = [
    //         'lob' => 'required|string|max:255',
    //         'section' => 'required|string|max:255',
    //         'sst' => 'required|string|max:255',
    //         'id' => 'required|string|max:255',
    //         'field' => 'required|string|max:255',
    //     ];
    //     $validator = Validator::make($request->all(), $rules);
    //     if ($validator->fails()) {
    //         return response()->json(
    //             [
    //                 'status' => 500,
    //                 'return_data' => [],
    //                 'message' => 'Validation fails',
    //                 'errors' => $validator->errors(),
    //             ],
    //             500
    //         );
    //     } else {
    //         // $status = StatusMaster::find($id);
    //         // $status = StatusMaster::where('status_id', $id)->first();
    //         // $status = StatusMaster::findOrFail($id);

    //         $AllField = SectionField::find($request->id);
    //         if ($AllField) {
    //             $AllField->update($request->all());

    //             return response()->json(
    //                 [
    //                     'status' => 200,
    //                     'return_data' => [],
    //                     'message' => 'Status Updated Successfully',
    //                 ],
    //                 200
    //             );
    //         } else {
    //             return response()->json(
    //                 [
    //                     'status' => 500,
    //                     'return_data' => [],
    //                     'message' => 'Status not found',
    //                 ],
    //                 500
    //             );
    //         }
    //     }
    // }

    public function updateField(Request $request)
    {
        $rules = [
            'lob' => 'required|string|max:255',
            'section' => 'required|string|max:255',
            'sst' => 'required|string|max:255',
            'id' => 'required|string|max:255',
            'field' => 'required|string|max:255',
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json([
                'status' => 500,
                'message' => 'Validation fails',
                'errors' => $validator->errors(),
            ], 500);
        }

        $AllField = SectionField::find($request->id);
        if ($AllField) {
            $AllField->update([
                'lob' => $request->lob,
                'section_name' => $request->section,
                'service_support_type' => $request->sst,
                'section_field_name' => $request->field,
            ]);

            return response()->json([
                'status' => 200,
                'message' => 'Field Updated Successfully',
            ], 200);
        } else {
            return response()->json([
                'status' => 500,
                'message' => 'Field not found',
            ], 500);
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(request $request)
    {

        $status = StatusMaster::findOrFail($request->id);
        $status->delete();

        return response()->json(['message' => 'Status deleted successfully']);

    }
    public function destroySst(request $request)
    {

        // dd($request->all());
        $AllSst = ServiceSupportType::findOrFail($request->id);
        $AllSst->delete();

        return response()->json(['message' => 'Status deleted successfully']);

    }
    public function destroySection(request $request)
    {

        $AllSection = section::findOrFail($request->id);
        $AllSection->delete();

        return response()->json(['message' => 'Section deleted successfully']);

    }
    public function destroyField(request $request)
    {

        $AllField = SectionField::findOrFail($request->id);
        $AllField->delete();

        return response()->json(['message' => 'Section deleted successfully']);

    }

}
