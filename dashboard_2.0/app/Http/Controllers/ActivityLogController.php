<?php

namespace App\Http\Controllers;

use App\Models\ActivityLog;
use Illuminate\Http\Request;
use App\Exports\AllDataExport;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;

class ActivityLogController extends Controller
{
    public function getActivityLogData(Request $request) 
    {
        $decryptedName = [];
        $query = ActivityLog::query();
        
        if (!$request->has('id') && !$request->has('user_id') && !$request->has('description') && !$request->has('start_date') && !$request->has('end_date')) {
            $query->orderBy('updated_at', 'desc'); 
        }
        if ($id = $request->input('id')) {
            $activityLog = $query->find($id);
            if (!$activityLog) {
                return response()->json([
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Record not found for this Id'
                ]);
            }
            return response()->json([
                'status' => 200,
                'return_data' => $activityLog,
                'message' => 'Record found'
            ]);
        }

        if ($userId = $request->input('user_id')) {
            $query->whereIn('subject_id', $userId);
            $userIds = (array) $userId; 
            if (!empty($userIds)) {
            }
        }

        if ($description = $request->input('description')) {
            if ($description === 'all') {
            } elseif (in_array($description, ['created', 'updated', 'deleted'])) {
            $query->where('description', $description);
            }
        }

        if ($request->has('start_date') && $request->has('end_date')) {
            $query->whereBetween('activity_log.created_at', [$request->start_date, $request->end_date]);
        }

        $perPage = $request->input('size') ?? 10;

        $limit = $request->input('limit');
        $offset = $request->input('offset') ?? null;
        
        if ($limit === null && $perPage !== null) {
            $limit = $perPage; // Use per_page as the limit if limit isn't provided and (page)
        }
    
        if ($limit !== null) {
            $query->limit($limit);
        }
    
        if ($offset !== null) {
            $query->offset($offset);
        }
    
        $activityLogs = $request->input('isPagination',true) ? 
            $query->join('users', 'activity_log.subject_id', '=', 'users.id')
                ->select('activity_log.*', 
                        'users.name as subject_name', 'users.name as causer_name',
                        'users.email as causer_email')
                ->paginate($perPage) :
            $query->join('users', 'activity_log.subject_id', '=', 'users.id')
                ->select('activity_log.*', 
                        'users.name as subject_name', 'users.name as causer_name',
                        'users.email as causer_email')
                ->orderby('updated_at','desc')
                ->get();


            foreach ($activityLogs as $user) {
                $properties = $user->properties;
                $oldProperties = " ";
                $newProperties = " ";
    
                if (preg_match('/"old":\s*(\{.*?\}),/', $properties, $matchesOld)) {
                    $oldProperties = $matchesOld[1]; 
                }
                
                if (preg_match('/"attributes":\s*(\{.*?\})/', $properties, $matchesNew)) {
                    $newProperties = $matchesNew[1]; 
                }
                $decryptedUser = [
                    'id' => $user->id,
                    'email' => credential_decrypt($user->email),
                    "log_name" =>$user->log_name,
                    "description" =>$user->description ,
                    "subject_type" =>$user->subject_type ,
                    "event" =>$user->event ,
                    "subject_id" =>$user->subject_id ,
                    "causer_type" => $user->causer_type ,
                    "causer_id" =>$user->causer_id ,
                    "old" => $oldProperties, 
                    "new" => $newProperties, 
                    "batch_uuid"=>$user->batch_uuid ,
                    "created_at"=>$user->created_at,
                    "updated_at"=>$user->updated_at ,
                    'subject_name' => credential_decrypt($user->subject_name),
                    'causer_name' => credential_decrypt($user->causer_name),
                    'causer_email' => credential_decrypt($user->causer_email),
                ];
                $decryptedName[] = $decryptedUser;
            }


        if ($decryptedName === []) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Record Not Found'
            ]);
        }

        if ($request->input('export') && $request->export == true) {

            $headings = ['id',
                        'log_name', 
                        'description',  
                        'subject_type',
                        'event',
                        'subject_id',
                        'causer_type',
                        'causer_id',
                        'properties',
                        'batch_uuid',
                        'created_at',
                        'updated_at'];
            $queryColumns = ['column_name_1', 'column_name_2'];

            $export = new AllDataExport($request, ActivityLog::class, $headings,$queryColumns );
            $filePath = 'Data/Activity_Log.xlsx';
            Excel::store($export, $filePath, 'public');
            $downloadLink = Storage::disk('public')->url($filePath);

            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }

        $responseData = [
            'status' => 200,
            "column_head"=> [
            [
                "header"=> "Subject_Name",
                "accessorKey"=> "subject_name",
                "isActions"=> false,
                "type" => "string"
            ],
            [
                "header"=> "Event",
                "accessorKey"=> "event",
                "isActions"=> false,
                "type" => "string"
            ],
            [
                "header"=> "Causer_Name",
                "accessorKey"=> "causer_name",
                "isActions"=> false,
                "type" => "string"
            ],
            [
                "header"=> "Created_At",
                "accessorKey"=> "created_at",
                "isActions"=> false,
                "type" => "date"
            ]
            ],
            'return_data' => $decryptedName,
            'message' => 'Records Found'
                    ];
        if ($request->input('isPagination')) {
            $responseData['pagination'] = [
                "pagination_type" => true,
                "per_page" => $activityLogs->perPage(),
                "prev_page_page" => $activityLogs->previousPageUrl(),
                "next_page_page" => $activityLogs->nextPageUrl(),
                "total" => $activityLogs->total(),
                "last_page" => $activityLogs->lastPage(),
            ];
        }

        return response()->json($responseData);
    }
}
