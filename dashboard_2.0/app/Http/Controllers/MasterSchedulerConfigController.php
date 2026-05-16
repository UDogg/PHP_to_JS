<?php

namespace App\Http\Controllers;
use App\Models\MasterSchedulerConfig;
use App\Models\MisReportConfigurator;
use App\Models\userTypes;
use Illuminate\Support\Str;
use Illuminate\Http\Request;
use Illuminate\Support\Carbon;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Validator;

class MasterSchedulerConfigController extends Controller
{
    public function getSchedularData(Request $request)
    {
        $column_head_data =[
            [
                "header"=> "Sr No",
                "accessorKey"=> "sr_no",
                "isActions"=> false,
            ],
            [
                "header"=> "Scheduler Name",
                "accessorKey"=> "scheduler_name",
                "isActions"=> false,
            ],
            [
                "header"=> "Template Name",
                "accessorKey"=> "template_name",
                "isActions"=> false,
            ],
            [
                "header"=> "Frequency",
                "accessorKey"=> "frequency",
                "isActions"=> false,
            ],
            [
                "header"=> "Starts On",
                "accessorKey"=> "starts_on",
                "isActions"=> false
            ],
            [
                "header"=> "Ends On",
                "accessorKey"=> "ends_on",
                "isActions"=> false
            ],
            [
                "header"=> "User Type",
                "accessorKey"=> "user_type_name",
                "isActions"=> false
            ],
            [
                "header"=> "Based On",
                "accessorKey"=> "based_on",
                "isActions"=> false
            ],
            [
                "header"=> "Status On",
                "accessorKey"=> "status_on",
                "isActions"=> false
            ],
            [
                "header"=> "Schedule Time",
                "accessorKey"=> "schedule_time",
                "isActions"=> true
            ],
            [
                "header"=> "Actions",
                "accessorKey"=> "actions",
                "isActions"=> true
            ],
        ];

        $page = $request->input('page', 1);
        $perPage = $request->input('show', 10);

    if ($request->has('paginate') && $request->paginate == true) {
        $paginatedData = MasterSchedulerConfig::paginate($perPage);

        $result = $paginatedData->map(function ($data,$index) use($page,$perPage) {
            return $this->transformSchedulerData($data, $index ,$page,$perPage);
        });

        $prevPage = $paginatedData->currentPage() - 1;
        $nextPage = $paginatedData->currentPage() + 1;

        // Return the paginated response with pagination metadata
        return response()->json([
            'status' => 200,
            'column_head' => $column_head_data, 
            'data' => $result,
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
        $datas = MasterSchedulerConfig::all();

        $result = $datas->map(function ($data, $index) use($page,$perPage)  {
            return $this->transformSchedulerData($data, $index,$page,$perPage);
        });

        return response()->json([
            'status' => 200,
            'column_head' => $column_head_data, 
            'data' => $result,
            'message' => 'Records Found',
        ]);
    }
    }

    private function transformSchedulerData($data, $index,$page,$perPage )
    {
        $templeteName = MisReportConfigurator::where('mis_report_configurator_id', $data->template_name)
            ->pluck('template_name')
            ->first();
        $userTypeName = userTypes::where('id', $data->user_type)
            ->pluck('name')
            ->first();
        $roleName = DB::table('roles')
            ->where('id', $data->roles)
            ->pluck('name')
            ->first();

        $formattedStartDate = Carbon::parse($data->starts_on)->format('d/m/Y');
        $formattedEndDate = $data->ends_on ? Carbon::parse($data->ends_on)->format('d/m/Y') : null;

        return [
            "sr_no" => (($page - 1) * $perPage) + (++$index),
            "id" => $data->id,
            "scheduler_name" => $data->scheduler_name,
            "template_id" => $data->template_name,  // Template ID
            "template_name" => $templeteName,
            "frequency" => $data->frequency,
            "starts_on" => $formattedStartDate,
            "every" => $data->every ?? null,
            "period" => $data->period ?? null,
            "expire_on" => $data->expire_on,
            "ends_on" => $formattedEndDate,
            "user_type_id" => $data->user_type,  // User type ID
            "user_type_name" => $userTypeName,
            "based_on" => $data->based_on,
            "role_id" => $data->roles ?? null,
            "roles" => $roleName ?? null,
            "email" => $data->email,
            "schedule_time" => $data->schedule_time
        ];
    }
    
    public function create(Request $request)
    {
        $createPermission = "Report Scheduler.edit";
        if (!auth()->user()->can($createPermission)) {
            return response()->json([
                'message' => 'You do not have permission to create.',
            ], 403);
        }
        $rules = [
            'scheduler_name' => 'required|string|max:255',
            'template_name' => 'required|integer',
            'frequency'      => 'required|string',
            'every'         => 'nullable|int',
            'period'         => 'nullable|string',
            // 'starts_on'      => 'required|date',
            'expire_on'      => 'required|string',
            // 'ends_on'         => 'nullable|date',
            'user_type'      => 'required|int',
            'based_on'       => 'required|string',
            'roles'          => 'nullable',
            'email'          => 'required|string'
        ];
   
        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json([
                'message' => 'Validation failed!',
                'errors'  => $validator->errors(),
            ], 422);
        }
    
         $formatted_starts_on = Carbon::createFromFormat('d/m/Y', $request->starts_on)->format('Y-m-d');
         if($request->ends_on != null){
             $formatted_ends_on =  Carbon::createFromFormat('d/m/Y', $request->ends_on)->format('Y-m-d');
         }

        $formatted_report_start_date = $request->report_start_date
            ? Carbon::createFromFormat('d/m/Y', $request->report_start_date)->format('Y-m-d')
            : null;

        $formatted_report_end_date = $request->report_end_date
            ? Carbon::createFromFormat('d/m/Y', $request->report_end_date)->format('Y-m-d')
            : null;

         $scheduler = new MasterSchedulerConfig();
         $scheduler->scheduler_name = $request->scheduler_name;
         $scheduler->template_name = $request->template_name;
         $scheduler->frequency = $request->frequency;
         $scheduler->starts_on = $formatted_starts_on ;
         $scheduler->every = $request->every ?? null; 
         $scheduler->period = $request->period ?? null; 
         $scheduler->expire_on = $request->expire_on; 
         $scheduler->ends_on = $formatted_ends_on ?? null ;  
         $scheduler->user_type = $request->user_type;
         $scheduler->based_on = $request->based_on;
         $scheduler->roles = $request->roles; 
         $scheduler->email = $request->email ?? null;
         $scheduler->schedule_time = $request->schedule_time;
         $scheduler->report_start_date = $formatted_report_start_date;
         $scheduler->report_end_date = $formatted_report_end_date;
         $scheduler->save();


        return response()->json([
            'message' => 'Data created successfully!',
            'data'    => $scheduler,
        ], 200);
    }

    public function edit(Request $request){

        $id = $request->id;   
        $datas = MasterSchedulerConfig::where('id',$id)->select('*')->get();
        $result = $datas->map(function ($data) {
            $templeteName= MisReportConfigurator::where('mis_report_configurator_id',$data->template_name)->pluck('template_name')->first();
            $userTypeName = userTypes::where('id',$data->user_type)->pluck('name')->first();
            $roleName = DB::table('roles')
            ->where('id', $data->roles)
            ->pluck('name')
            ->first();

            $getStartOn=$data->starts_on;
            if($data->ends_on != null){
                $getEndsOn=$data->ends_on;
                $formattedEndDate = Carbon::parse($getEndsOn)->format('d/m/Y');
            }

            $formattedStartDate = Carbon::parse($getStartOn)->format('d/m/Y');

                return [
                    "id" => $data->id,
                    "scheduler_name" => $data->scheduler_name,
                    "template_id" => $data->template_name,  //template id will getted
                    "template_name" => $templeteName,
                    "frequency" => $data->frequency,
                    "starts_on" => $formattedStartDate,
                    "every" => $data->every ?? null,
                    "period" => $data->period ?? null,
                    "expire_on" => $data->expire_on,
                    "ends_on" => $formattedEndDate ?? null,
                    "user_type_id" => $data->user_type,  //user type id will be getted
                    "user_type_name" => $userTypeName,
                    "based_on" => $data->based_on,
                    "role_id" => $data->roles ?? null,
                    "roles" => $roleName ?? null,
                    "email" => $data->email,
                ];

    }

     );


        return response()->json($result);



    }

    public function update(Request $request){
       
        $createPermission = "Report Scheduler.edit";
        if (!auth()->user()->can($createPermission)) {
            return response()->json([
                'message' => 'You do not have permission to create.',
            ], 403);
        }

        $formatted_starts_on = Carbon::createFromFormat('d/m/Y', $request->starts_on)->format('Y-m-d');
        if($request->ends_on != null){
            $formatted_ends_on =  Carbon::createFromFormat('d/m/Y', $request->ends_on)->format('Y-m-d');
        }

        $formatted_report_start_date = $request->report_start_date
            ? Carbon::createFromFormat('d/m/Y', $request->report_start_date)->format('Y-m-d')
            : null;

        $formatted_report_end_date = $request->report_end_date
            ? Carbon::createFromFormat('d/m/Y', $request->report_end_date)->format('Y-m-d')
            : null;

        $data = MasterSchedulerConfig::find($request->id);
        $data->scheduler_name = $request->scheduler_name;
        $data->template_name = $request->template_name;
        $data->frequency = $request->frequency;
        $data->every = $request->every ?? null;
        $data->period = $request->period ?? null;
        $data->starts_on = $formatted_starts_on;
        $data->expire_on = $request->expire_on ;
        $data->ends_on = $formatted_ends_on ?? null; 
        $data->user_type = $request->user_type;
        $data->based_on = $request->based_on;
        $data->roles = $request->roles; 
        $data->email = $request->email ?? null;
        $data->schedule_time = $request->schedule_time;
        $data->report_start_date = $formatted_report_start_date;
        $data->report_end_date = $formatted_report_end_date;
        $data->save();

        // $data->update($validator->validated());

        return response()->json([
            'message' => 'Data updated successfully!',
            'data'    => $data
        ], 200);
    }

    public function delete(Request $request){

        $deletePermission = "Report Scheduler.delete";
        if (!auth()->user()->can($deletePermission)) {
            return response()->json([
                'message' => 'You do not have permission to delete.',
            ], 403);
        }
        
        $data = MasterSchedulerConfig::find($request->id);
        $data->delete();

        return response()->json([
            'message' => 'Data deleted successfully!',
            'data'    => $data
        ], 200);

        
    }
    
}
