<?php

namespace App\Http\Controllers;

use App\Models\userTypes;
use Illuminate\Http\Request;
use Illuminate\Validation\Rule;
use App\Exports\OfflinePolicyData;
use Illuminate\Support\Facades\DB;
use App\Models\OfflineUploadPolicy;
use Illuminate\Support\Facades\Auth;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;

class OfflineUploadPolicyController extends Controller
{
    public function index(Request $request)
    {
        $userId = Auth::id();
        $isAdmin = UserIsAdmin($userId);
        if (!$isAdmin) {
            return response()->json(['error' => 'Unauthorized'], 403);
        }
        $export    = $request->boolean('export');
        $page      = (int) $request->input('page', 1);
        $perPage   = (int) $request->input('size', 10);
        $search    = $request->input('search');
        $startDate = $request->input('start_date');
        $endDate   = $request->input('end_date');
    
        $query = OfflineUploadPolicy::query();
    
        if ($search) {
            $query->where(function ($q) use ($search) {
                $q->whereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.policy_no'))) LIKE ?", ['%' . strtolower($search) . '%'])
                ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.customer_name'))) LIKE ?", ['%' . strtolower($search) . '%'])
                ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.mobile'))) LIKE ?", ['%' . strtolower($search) . '%'])
                ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.status'))) LIKE ?", ['%' . strtolower($search) . '%'])
                ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.ic_name'))) LIKE ?", ['%' . strtolower($search) . '%'])
                ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.reg_no'))) LIKE ?", ['%' . strtolower($search) . '%']);
            });
        }
    
        if ($startDate) {
            $query->whereDate('created_at', '>=', $startDate);
        }
    
        if ($endDate) {
            $query->whereDate('created_at', '<=', $endDate);
        }

        if ($export) {
            $data = $query->orderBy('created_at', 'desc')->get();
    
            $filePath = 'exports/OfflineUploadPolicy_' . now()->format('Y_m_d_His') . '.xlsx';
            Excel::store(new OfflinePolicyData($data), $filePath, 'public');
            $downloadLink = asset(Storage::url($filePath));
    
            return response()->json([
                'message' => 'Export successful.',
                'download_url' => $downloadLink,
            ]);
        }
    
        $policies = $query->orderBy('created_at', 'desc')
                        ->paginate($perPage, ['*'], 'page', $page);
    
        $dataWithUrls = collect($policies->items())->map(function ($policy) {
            $data = $policy->data;
        
            return [
                'id'         => $policy->id,
                'created_at' => $policy->created_at,
                'updated_at' => $policy->updated_at,
                'data'       => $data,
            ];
        })->toArray();
        
        $columnHead = [];
        if (!empty($dataWithUrls)) {
            $firstData = $dataWithUrls[0]['data'] ?? [];
        
            foreach ($firstData as $key => $value) {
                $columnHead[] = [
                    'header'       => ucwords(str_replace('_', ' ', $key)),
                    'accessorKey'  => $key,
                    'type'         => gettype($value),
                ];
            }
        }
                        
    
        return response()->json([
            'message' => 'Policy list retrieved successfully.',
            'return_data' => $dataWithUrls,
            'column_head' => $columnHead,
            'pagination' => [
                'total_records' => $policies->total(),
                'size' => $policies->perPage(),
                'current_page' => $policies->currentPage(),
                'total_pages' => $policies->lastPage(),
            ],
        ]);
    }
     
    
    /**
     * Show the form for creating a new resource.
     */
    // public function create()
    // {
    //     //
    // }

    public function store(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'data.customer_name' => 'required|string',
            'data.mobile'        => 'required|string',
            'data.email'         => 'nullable|email',
            'data.reg_no'        => 'required|string',
            'data.ic_name'       => 'required|string',
            'data.policy_no'     => 'required|string|alpha_num',
            'data.policy_type'   => 'required|string',
            'policy_copy_doc'        => 'nullable|file|mimes:pdf,jpg,png|max:5120',
            'previous_policy_copy'   => 'nullable|file|mimes:pdf,jpg,png|max:5120',
            'rc_copy'                => 'nullable|file|mimes:pdf,jpg,png|max:5120',
        ]);

        $validator->after(function ($validator) use ($request) {
            $exists = DB::table('offline_upload_policy')
                ->whereRaw("json_unquote(json_extract(data, '$.policy_no')) = ?", [$request->input('data.policy_no')])
                ->exists();

            if ($exists) {
                $validator->errors()->add('data.policy_no', 'The policy number has already been taken.');
            }
        });

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 422);
        }

        $data = $request->input('data', []);
        $data['created_by'] = Auth::id();

        if ($request->hasFile('policy_copy_doc')) {
            $file = $request->file('policy_copy_doc');
            $filename = time() . '_' . $file->getClientOriginalName();
            $path = $file->storeAs('OfflinePolicyList', $filename, 'public');
            $data['policy_copy_doc_path'] = asset(Storage::url($path));
        }

        if ($request->hasFile('previous_policy_copy')) {
            $file = $request->file('previous_policy_copy');
            $filename = time() . '_' . $file->getClientOriginalName();
            $path = $file->storeAs('OfflinePolicyList', $filename, 'public');
            $data['previous_policy_copy_path'] = asset(Storage::url($path));
        }

        if ($request->hasFile('rc_copy')) {
            $file = $request->file('rc_copy');
            $filename = time() . '_' . $file->getClientOriginalName();
            $path = $file->storeAs('OfflinePolicyList', $filename, 'public');
            $data['rc_copy_path'] = asset(Storage::url($path));
        }

        $policy = OfflineUploadPolicy::create([
            'data' => $data,
        ]);

        return response()->json([
            'message' => 'Policy created successfully.',
            'return_data' => [
                'id' => $policy->id,
                'created_at' => $policy->created_at,
                'updated_at' => $policy->updated_at,
                'data' => $policy->data,
            ],
        ], 201);
    }



    public function update(Request $request, $id)
    {
        $policy = OfflineUploadPolicy::findOrFail($id);

        $rules = [
            'customer_name' => 'required|string|max:255',
            'mobile' => 'required|string|max:15',
            'email' => 'required|email',
            'reg_no' => 'required|string|max:20',
            'ic_name' => 'required|string|max:255',
            'policy_no' => 'required|string|max:255',
            'policy_type' => 'required|string|max:10',
            'tp_start_date' => 'required|date',
            'tp_end_date' => 'required|date|after:tp_start_date',
            'status' => 'nullable|string',
        ];

        $data = $request->all();
        $validator = Validator::make($data, $rules);

        if ($validator->fails()) {
            return response()->json([
                'errors' => $validator->errors()
            ], 422);
        }

        $existingData = $policy->data ?? [];
        $mergedData = array_merge($existingData, $data);

        $policy->update([
            'data' => $mergedData,
        ]);

        return response()->json([
            'message' => 'Policy updated successfully.',
            'data' => $policy,
        ]);
    }

    public function offlinePolicyStatus(Request $request, $id)
    {
        $policy = OfflineUploadPolicy::findOrFail($id);

        $rules = [
            'status' => 'required|string',
            'discrepancy_message' => 'nullable|string',
            'rejected_message' => 'nullable|string',
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json([
                'errors' => $validator->errors()
            ], 422);
        }

        $updateData = [
            'status' => $request->input('status'),
            'discrepancy_message' => $request->input('discrepancy_message'), 
            'rejected_message' => $request->input('rejected_message'),
        ];

        $existingData = $policy->data ?? [];
        $mergedData = array_merge($existingData, $updateData);

        $policy->update([
            'data' => $mergedData,
        ]);

        return response()->json([
            'message' => 'Policy status updated successfully.',
            'data' => $policy,
        ]);
    }



    // /**
    //  * Display the specified resource.
    //  */
    // public function show(string $id)
    // {
    //     //
    // }

    /**
     * Show the form for editing the specified resource.
     */
    // public function edit(string $id)
    // {
        
    // }

    public function offlinePolicyDoc(Request $request)
    {
        $policy = OfflineUploadPolicy::findOrFail($request->id);
        $data = $policy->data ?? [];
    
        if ($request->hasFile('policy_copy_doc')) {
            $file = $request->file('policy_copy_doc');
            $filename = time() . '_' . $file->getClientOriginalName();
            $path = $file->storeAs('OfflinePolicyList', $filename, 'public');
            $data['policy_copy_doc_path'] = asset(Storage::url($path));
        }
    
        if ($request->hasFile('previous_policy_copy')) {
            $file = $request->file('previous_policy_copy');
            $filename = time() . '_' . $file->getClientOriginalName();
            $path = $file->storeAs('OfflinePolicyList', $filename, 'public');
            $data['previous_policy_copy_path'] = asset(Storage::url($path));
        }
    
        if ($request->hasFile('rc_copy')) {
            $file = $request->file('rc_copy');
            $filename = time() . '_' . $file->getClientOriginalName();
            $path = $file->storeAs('OfflinePolicyList', $filename, 'public');
            $data['rc_copy_path'] = asset(Storage::url($path));
        }
    
        if ($request->hasFile('policy_copy_doc') || $request->hasFile('previous_policy_copy') || $request->hasFile('rc_copy')) {
            $policy->update([
                'data' => $data,
            ]);
        }
    
        return response()->json([
            'message' => 'Files checked and policy updated successfully.',
            'data' => $policy,
        ]);
    }


    public function showPolicyList(Request $request)
    {
        $user = Auth::user();
        $usertypeid = $user->usertype;
        $isAdmin = $user->is_admin;
        $status = $request->input('status');
        $export = $request->boolean('export'); 
        $startDate = $request->input('start_date');
        $endDate = $request->input('end_date');

        $usertype = userTypes::select('Identifier')->where('id', $usertypeid)->first();
        $identifier = $usertype->Identifier ?? null;

        if (($identifier === 'P' || $identifier === 'E') && $isAdmin === 'N') {
            $page = (int) $request->input('page', 1);
            $perPage = (int) $request->input('size', 10);
            $search = $request->input('search');

            $query = OfflineUploadPolicy::query();

            if (!empty($status)) {
                $query->whereRaw("LOWER(TRIM(JSON_UNQUOTE(JSON_EXTRACT(data, '$.status')))) = ?", [strtolower(trim($status))]);
            }

            if ($startDate) {
                $query->whereDate('created_at', '>=', $startDate);
            }

            if ($endDate) {
                $query->whereDate('created_at', '<=', $endDate);
            }

            if (!empty($search)) {
                $searchTerm = '%' . strtolower(trim($search)) . '%';
                $query->where(function ($q) use ($searchTerm) {
                    $q->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.policy_no'))) LIKE ?", [$searchTerm])
                    ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.customer_name'))) LIKE ?", [$searchTerm])
                    ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.mobile'))) LIKE ?", [$searchTerm])
                    ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.status'))) LIKE ?", [$searchTerm])
                    ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.ic_name'))) LIKE ?", [$searchTerm])
                    ->orWhereRaw("LOWER(JSON_UNQUOTE(JSON_EXTRACT(data, '$.reg_no'))) LIKE ?", [$searchTerm]);
                });
            }

            $query->orderBy('created_at', 'desc');

            if ($export) {
                $data = $query->get();
                $filePath = 'exports/OfflineUploadPolicy_' . now()->format('Y_m_d_His') . '.xlsx';
                Excel::store(new OfflinePolicyData($data), $filePath, 'public');
                $downloadLink = asset(Storage::url($filePath));

                return response()->json([
                    'message' => 'Export successful.',
                    'download_url' => $downloadLink,
                ]);
            }

            $policies = $query->paginate($perPage, ['*'], 'page', $page);

            $dataWithUrls = collect($policies->items())->map(function ($policy) {
                return [
                    'id'         => $policy->id,
                    'created_at' => $policy->created_at,
                    'updated_at' => $policy->updated_at,
                    'data'       => $policy->data,
                ];
            })->toArray();

            $columnHead = [];
            if (!empty($dataWithUrls)) {
                $firstData = $dataWithUrls[0]['data'] ?? [];
                foreach ($firstData as $key => $value) {
                    $columnHead[] = [
                        'header'      => ucwords(str_replace('_', ' ', $key)),
                        'accessorKey' => $key,
                        'type'        => gettype($value),
                    ];
                }
            }

            return response()->json([
                'message' => 'Policy list retrieved successfully.',
                'return_data' => $dataWithUrls,
                'column_head' => $columnHead,
                'pagination' => [
                    'total_records' => $policies->total(),
                    'size' => $policies->perPage(),
                    'current_page' => $policies->currentPage(),
                    'total_pages' => $policies->lastPage(),
                ],
            ]);
        }

        return response()->json(['error' => 'Unauthorized'], 403);
    }


     
    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $policy = OfflineUploadPolicy::findOrFail($id);
        $policy->delete();

        return response()->json([
            'message' => 'Policy deleted successfully.',
        ]);
    }
}
