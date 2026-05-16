<?php

namespace App\Http\Controllers\ReportConfigurator;

use Carbon\Carbon;
use App\Models\User;
use App\Models\userTypes;
use App\Models\KeyUtility;
use Illuminate\Http\Request;
use App\Models\DataExportLog;
use App\Models\TemplateModel;
use Illuminate\Validation\Rule;
use Illuminate\Support\Facades\DB;
use App\Http\Controllers\Controller;
use Illuminate\Support\Facades\Auth;
use App\Models\MisReportConfigurator;
use App\Models\TemplateRelationModel;
use Illuminate\Support\Facades\Storage;
use App\Models\GroupingReportKeyUtility;
use SebastianBergmann\Template\Template;
use Illuminate\Support\Facades\Validator;

class GroupingReportKeyUtilityController extends Controller
{
    public function index()
    {
        $key_utility = KeyUtility::select('id', 'key')->get();
        $group_report = GroupingReportKeyUtility::select('key_utility_report_id', 'key', 'key_utility_id')->get()->all();
        $group_report_data = KeyUtility::select('key_utility.id', 'key_utility.key', 'k.key as sub', 'k.key_utility_report_id')->join('key_utility_report as k', 'k.key_utility_id', 'key_utility.id')->whereNull('k.deleted_at')->orderBy('k.updated_at')->get
        ();
        $group_report_data = collect($group_report_data)->groupBy('sub');
        return view('keyutilityreport', compact('key_utility', 'group_report', 'group_report_data'));
    }
    public function store(Request $request)
    {
        $rules = [
            'key_name' => 'required|string|max:100',
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'validations fails',
                    'errors' => $validator->errors()
                ],
                500
            );
        } else {

            $exsiting_columns=GroupingReportKeyUtility::where('key', $request->key_name)->pluck('key_utility_id')->toArray();

            $unique = array_values(array_diff($request->columns, $exsiting_columns));
 
            $request->merge(['columns' => $unique]);

            foreach ($request->columns as $key) {
                $grouping_report = new GroupingReportKeyUtility();
                $grouping_report->key = $request->key_name;
                $key_id  = $key;
                $grouping_report->key_utility_id = $key_id;
                $grouping_report->save();
            }
            if ($grouping_report) {
                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => [],
                        'message' => 'Data fetched successfully',

                    ],
                    200
                );
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Something went wrong',
                    ],
                    500
                );
            }
        }
    }

    public function edit(Request $request,$name){
        $exsiting_column_id=GroupingReportKeyUtility::where('key', $name)->pluck('key_utility_id')->toArray();
        $key_utility = KeyUtility::select('id', 'key')->get();
        $common_name = $name;

          return view('keyutilityreportEditPage', compact('key_utility', 'exsiting_column_id','common_name' ));

    }

    public function updatePriority(Request $request)
    {
        $order = $request->input('order');
        foreach ($order as $item) {
            DB::table('key_utility_report')
                ->where('key_utility_report_id', $item['id'])
                ->update(['priority' => $item['priority']]);
        }

        return response()->json(['status' => 'success']);
    }
    public function update(Request $request, $name)
    {
        $columns = $request->columns;

        GroupingReportKeyUtility::where('key', $name)->delete();

        foreach ($columns as $index => $col) {
            GroupingReportKeyUtility::create([
                'key' => $name,
                'key_utility_id' => $col,
            ]);
        }

        return redirect()->route('reportKeyUtility.index')
            ->with('success', 'Updated successfully');
    }
    public function delete(Request $request)
    {
        $records = GroupingReportKeyUtility::where('key', $request->input('key'))->get();
        $deleteResults = [];
        foreach ($records as $record) {
            $deleteResults[] = $record->delete();
        }

        if (in_array(false, $deleteResults, true)) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Some records could not be deleted',
                ],
                500
            );
        }
        return response()->json(
            [
                'status' => 200,
                'return_data' => [],
                'message' => 'All data deleted successfully',
            ],
            200
        );
    }
    public function deleteSinglekey(Request $request)
    {
        $records = GroupingReportKeyUtility::where('key_utility_report_id', $request->input('key'))->first();
        if ($records->delete()) {
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'All data deleted successfully',
                ],
                200
            );
        } else {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Some records could not be deleted',
                ],
                500
            );
        }
    }
    public function misReportGroupGetData(Request $request)
    {
        $insert = MisReportConfigurator::create($request->all());
        if ($insert) {
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [],
                    'message' => 'Data Added successfully',
                ],
                200
            );
        } else {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Something went wrong',
                ],
                500
            );
        }
    }
  
    public function createTemplate(Request $request)
    {
        $user = Auth::user();
        $createPermission = "Report Template List.edit";
        if(!$user->can($createPermission)){
            return response()->json(
                [
                    'status' => 403,
                    'return_data' => [],
                    'message' => 'You do not have permission to create a template',
                ],
                403
            );

        }
        if ($user) {
            $rules = [
                "lob" => "required",
                "role" => "required",
                "stage_id" => "required",
                "template_name" => "required|unique:mis_report_configurator,template_name",
                "sequence" => "required",
            ];
            $validator = Validator::make($request->all(), $rules);
            if ($validator->fails()) {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'validations fails',
                        'errors' => $validator->errors()
                    ],
                    500
                );
            } else {
                $user_type = userTypes::where('id',$request->user_type_id)->first();
                $data = $request->all();
                $template = new MisReportConfigurator();
                $template->template_name = $data['template_name'];
                $template->user_id = $user->id;
                $template->user_type = $user_type->name;
                $template->user_type_id =$user->usertype;
                $template->lob_id = isset($data['lob']) ? implode(',', $data['lob']) : null;
                $template->role_id = isset($data['role']) ? implode(',', $data['role']) : null;
                $template->stage_id = isset($data['stage_id']) ? implode(',', $data['stage_id']) : null;
                $template->columns = isset($data['columns']) ? json_encode($data['columns']) : null;
                $template-> static_columns = isset($data['staticColumns']) ? json_encode($data['staticColumns']) : null;
                $template->sequence = isset($data['sequence']) ? implode(',', $data['sequence']) : null;
                $template->stage_name = isset($data['stage_name']) ?  json_encode($data['stage_name']) : null;
                $template->save();
                if ($template) {
                    return response()->json(
                        [
                            'status' => 200,
                            'return_data' => [],
                            'message' => 'Template created successfully',
                        ],
                        200
                    );
                } else {
                    return response()->json(
                        [
                            'status' => 500,
                            'return_data' => [],
                            'message' => 'Something went wrong',
                        ],
                        500
                    );
                }
            }
        }
    }
    public function listTemplate(Request $request)
    {
        $lobValues = $request->lob;
        if($request->mis_report_configurator_id){
            $reportColumn=MisReportConfigurator::where('mis_report_configurator_id',$request->mis_report_configurator_id)->select('columns','static_columns')->first();
            $staticColumns =  json_decode($reportColumn->static_columns, true);
            $reportColumns = json_decode($reportColumn->columns, true);
            $templateList = GroupingReportKeyUtility::join('key_utility', 'key_utility.id', '=', 'key_utility_report.key_utility_id')
                ->leftJoin('key_utility_mapping', 'key_utility_mapping.key_id', '=', 'key_utility.id')
                ->leftJoin('policystatus_column_master', 'policystatus_column_master.id', '=', 'key_utility_mapping.mapping_id')
                ->select('key_utility_report.key', 'policystatus_column_master.column_name')
                ->whereIn('key_utility_mapping.lob', $lobValues)
                ->get()
                ->toArray();

            $mergedData = [];
            foreach ($templateList as $templateItem) {
                $reportKey = array_search($templateItem['column_name'], $reportColumns);
               
                if ($reportKey !== false) {
                    $mergedData[] = [
                        'key' => $templateItem['key'],
                        'column_name' => $templateItem['column_name'],
                        'report_key' => $reportKey 
                    ];
                } else {
                    
                    $mergedData[] = [
                        'key' => $templateItem['key'],
                        'column_name' => $templateItem['column_name']
                    ];
                }
            }
            $groupedData = collect($mergedData)->groupBy('key')->map(function ($items, $key) use ($reportColumns,$staticColumns) {
            $reportKeys = $items->pluck('report_key')->filter()->unique()->toArray();
                foreach ($reportColumns as $reportKey => $columnName) {
                    if (in_array($columnName, $items->pluck('column_name')->toArray())) {
                        if (!in_array($reportKey, $reportKeys)) {
                            $reportKeys[] = $reportKey;
                        }
                    }
                }
                return [
                    'key' => $key,
                    'column_names' => array_values($items->pluck('column_name')->unique()->toArray()),
                    'reportColumns'=> $reportColumns ,
                    'staticColumns'=> $staticColumns 
                ];
            })->values();
            return response()->json([
                'status' => 200,
                'return_data' => $groupedData->toArray(),
                'message' => 'Data Fetched successfully',
            ], 200);
        }
        $templateList = GroupingReportKeyUtility::join('key_utility', 'key_utility.id', '=', 'key_utility_report.key_utility_id')
        ->leftJoin('key_utility_mapping', 'key_utility_mapping.key_id', '=', 'key_utility.id')
        ->leftJoin('policystatus_column_master', 'policystatus_column_master.id', '=', 'key_utility_mapping.mapping_id')
        ->select('key_utility_report.key', 'policystatus_column_master.column_name')
        ->whereIn('key_utility_mapping.lob', $lobValues)
        ->get();
        if ($templateList->isEmpty()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Data Not found',
                ],
                500
            );
        } else {
            if ($templateList->isEmpty()) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Data Not found',
                ], 500);
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
            ], 200);
        }
    }
    public function getTemplate(Request $request)
    {
        $user=Auth::user();
        $user_id=$user->id;
        $role_id = Auth::user()->roles->pluck('id')->all();
        $query = MisReportConfigurator::select(
            'mis_report_configurator.mis_report_configurator_id',
            'mis_report_configurator.template_name',
            'mis_report_configurator.role_id',
            DB::raw("GROUP_CONCAT(DISTINCT roles.name ORDER BY roles.name) AS role_name"),
            DB::raw("GROUP_CONCAT(DISTINCT lob_master.lob ORDER BY lob_master.lob) AS lob_name"),
            'mis_report_configurator.lob_id',
            DB::raw("GROUP_CONCAT(DISTINCT mis_report_configurator.stage_name ORDER BY mis_report_configurator.stage_name) AS stage_name"),
            'mis_report_configurator.stage_id',
            'mis_report_configurator.user_id',
            'mis_report_configurator.user_type',
            'mis_report_configurator.user_type_id',
            'users.username as user_name'
        )
        ->leftJoin('roles', function($join) {
            $join->on(DB::raw('FIND_IN_SET(roles.id, mis_report_configurator.role_id)'), '>', DB::raw('0'));
        })
        ->leftJoin('lob_master', function($join) {
            $join->on(DB::raw('FIND_IN_SET(lob_master.id, mis_report_configurator.lob_id)'), '>', DB::raw('0'));
        })->leftJoin('users','users.id','mis_report_configurator.user_id')
        ->groupBy(
            'mis_report_configurator.mis_report_configurator_id',
            'mis_report_configurator.template_name',
            'mis_report_configurator.lob_id',
            'mis_report_configurator.stage_id',
            'mis_report_configurator.user_id',
            'mis_report_configurator.user_type',
            'mis_report_configurator.user_type_id',
            'users.username'
        )->where(function ($q) use ($user_id, $role_id) {
            $q->where('mis_report_configurator.user_id', $user_id);

            foreach ($role_id as $rId) {
                $q->orWhereRaw('FIND_IN_SET(?, mis_report_configurator.role_id)', [$rId]);
            }
        });

        if (isset($request->mis_report_configurator_id)) {
            $query->where('mis_report_configurator.mis_report_configurator_id', $request->mis_report_configurator_id);
        }
        
        $query->orderBy('mis_report_configurator.mis_report_configurator_id', 'desc');
        $template = $query->get();
    
        foreach ($template as $item) {
            $item->user_name = credential_decrypt($item->user_name); 
            $user_admin=UserIsAdmin($user_id);
            if($user_admin == true){
                $item->is_edit = 'Y'; 
                $item->is_delete = 'Y';
            }else{
                if ($item->user_id == $user_id) {
                    $item->is_edit = 'Y'; 
                    $item->is_delete = 'Y';
                } else {
                    $item->is_edit = 'N';
                    $item->is_delete = 'N';
                }
            }
            $stageNameArray = json_decode($item->stage_name, true);
            
            if (is_array($stageNameArray)) {
                $item->stage_name = implode(',', $stageNameArray);
            } else {
                $item->stage_name = $item->stage_name; 
            }
        }
        if ($template->isEmpty()) {
            return response()->json([
                'status' => 200,
                'return_data' => [],
                'message' => 'Data Not found',
            ], 200);
        } else {
            return response()->json([
                'status' => 200,
                'return_data' => $template,
                'message' => 'Data Fetched successfully',
            ], 200);
        }
    }
    public function EditTemplate(Request $request)
    {
        $request->validate([
            'template_name' => [
                'required',
                Rule::unique('mis_report_configurator')->ignore($request->mis_report_configurator_id, 'mis_report_configurator_id')
            ],
            'lob' => 'required',
            'role' => 'required',
            'stage_id' => 'required',
            'sequence' => 'required',
        ], [
            'template_name.unique' => 'This template name already exists. Please choose another name.',
        ]);
        $misReportConfigurator = MisReportConfigurator::where('mis_report_configurator_id', $request->mis_report_configurator_id)->first();
        //dd($request->lob);
        if ($misReportConfigurator) {
            $misReportConfigurator->template_name = $request->template_name ?? $misReportConfigurator->template_name;
            $misReportConfigurator->user_id = $request->user_id ?? $misReportConfigurator->user_id;
            $misReportConfigurator->user_type_id = $request->user_type_id ?? $misReportConfigurator->user_type_id;
            $misReportConfigurator->user_type = $request->user_type ?? $misReportConfigurator->user_type;
            $misReportConfigurator->lob_id = is_array($request->lob) ? implode(',', $request->lob) : ($request->lob ?? $misReportConfigurator->lob_id);
            $misReportConfigurator->stage_id = is_array($request->stage_id) ? implode(',', $request->stage_id) : ($request->stage_id ?? $misReportConfigurator->stage_id);
            $misReportConfigurator->role_id = is_array($request->role) ? implode(',', $request->role) : ($request->role ?? $misReportConfigurator->role_id);
            $misReportConfigurator->stage_name = is_array($request->stage_name) ? json_encode($request->stage_name) : ($request->stage_name ?? $misReportConfigurator->stage_name);
            $misReportConfigurator->sequence = is_array($request->sequence) ? implode(',', $request->sequence) : ($request->sequence ?? $misReportConfigurator->sequence);
            $misReportConfigurator->columns = is_array($request->columns) ? json_encode($request->columns) : ($request->columns ?? $misReportConfigurator->columns);
            $misReportConfigurator->static_columns = is_array($request->staticColumns) ? json_encode($request->staticColumns) : ($request->staticColumns ?? $misReportConfigurator->static_columns);
            $misReportConfigurator->save();
            return response()->json(
                [
                    'status' => 200,
                    'return_data' => [$misReportConfigurator],
                    'message' => 'Mis report template updated successfully',
                ],
                200
            );
        } else {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'something went wrong',
                ],
                500
            );
        }
    }
    public function DeleteTemplate(Request $request)
    {
        $user = Auth::user();
        $deletePermission = "Report Template List.delete";
        if(!$user->can($deletePermission)){
            return response()->json(
                [
                    'status' => 403,
                    'return_data' => [],
                    'message' => 'You do not have permission to delete a template',
                ],
                403
            );
        }
        $misReportConfigurator = MisReportConfigurator::where('mis_report_configurator_id', $request->mis_report_configurator_id)->delete();
       if($misReportConfigurator){
        return response()->json(
            [
                'status' => 200,
                'return_data' => [],
                'message' => 'Mis report template deleted successfully',
            ],
            200
        );
       }else{
        return response()->json(
            [
                'status' => 500,
                'return_data' => [],
                'message' => 'something went wrong',
            ],
            500
        );
       }
        
    }

    public function listReportData(Request $request)
    {

        $column_head_data = [
            [
                "header" => "Sr No",
                "accessorKey" => "sr_no",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "Template Name",
                "accessorKey" => "template_name",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "Start Date",
                "accessorKey" => "start_date",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "End Date",
                "accessorKey" => "end_date",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "Created On",
                "accessorKey" => "created_on",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "Created By",
                "accessorKey" => "created_by",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "Status",
                "accessorKey" => "status",
                "isActions" => false,
                "type" => "string"
            ],
            [
                "header" => "Actions",
                "accessorKey" => "actions",
                "isActions" => true,
                "type" => "string"
            ],
        ];
        $perPage = $request->input('show', 10);
        $page = $request->input('page', 1);


        if ($request->has('paginate') && $request->paginate == 'true') {

            $query = DataExportLog::query();
            if ($request->has('search') && !empty($request->search)) {
                $search = $request->search;
                $query->where(function ($q) use ($search) {
                    $q->where('source', 'like', "%$search%")
                        ->orWhere('status', 'like', "%$search%")
                        ->orWhere('file', 'like', "%$search%");
                });
            }

            $paginatedData = $query->paginate($perPage);

            $result = $paginatedData
                ->map(function ($data, $index) use ($page, $perPage) {
                    return $this->transformDataExportLog($data, $index, $page, $perPage);
                })
                ->filter(function ($data) {
                    return !empty($data['template_name']);
                });

            $prevPage = $paginatedData->currentPage() - 1;
            $nextPage = $paginatedData->currentPage() + 1;

            if ($result->isEmpty()) {
                return response()->json([
                    'status' => 404,
                    'message' => 'Data not found',
                    'data' => [],
                    'pagination' => null,
                ]);
            }


            // Return the paginated response with pagination metadata
            return response()->json([
                'status' => 200,
                'column_head' => $column_head_data,
                'data' => $result->values(),
                'message' => 'Records Found',
                'pagination' => [
                    'per_page' => $paginatedData->perPage(),
                    'page' => $paginatedData->currentPage(),
                    'prev_page' => $prevPage > 0 ? $prevPage : null, // Return null if there is no previous page
                    'next_page' => $nextPage <= $paginatedData->lastPage() ? $nextPage : null, // Return null if there is no next page
                    'total' => $paginatedData->total(),
                    'last_page' => $paginatedData->lastPage(),
                ]

            ]);
        } else {
            $datas = DataExportLog::all();

            $result = $datas->map(function ($data, $index) use ($page, $perPage) {
                return $this->transformDataExportLog($data, $index, $page, $perPage);
            });

            return response()->json([
                'status' => 200,
                'column_head' => $column_head_data,
                'data' => $result,
                'message' => 'Records Found',
            ]);
        }
    }

    private function transformDataExportLog($data, $index, $page, $perPage)
    {

        $formating_template_name = $data->file;
        $fileNameWithoutExtension = pathinfo($formating_template_name, PATHINFO_FILENAME); // Remove the file extension

        if (substr_count($fileNameWithoutExtension, '_') == 2) {

            $parts = explode('_', $fileNameWithoutExtension);   // Split the string by underscores
            $cleanedTemplateName = $parts[1]; // Get the name between the first and last underscore
        } else {
            $cleanedTemplateName = $fileNameWithoutExtension;
        }

        $file_link = Storage::disk('public')->url($data->file);
        $created_by_encrypted = User::where('id', $data->user_id)->pluck('name')->first();
        $created_by = credential_decrypt($created_by_encrypted);
        $date = $data->created_at;
        $formatted_start_date = $date->format('Y-m-d H:i:s');
        $date = Carbon::parse($formatted_start_date)->addDays(2);
        $formatted_end_date = $date->format('Y-m-d H:i:s');

        return [
            "sr_no" => (($page - 1) * $perPage) + (++$index),
            "template_name" => $cleanedTemplateName,
            "start_date" => $formatted_start_date,
            "end_date" => $formatted_end_date,
            "created_on" => $formatted_start_date,
            "created_by" => $created_by,
            "status" => $data->status,
            "actions" => $file_link,

        ];
    }



}
