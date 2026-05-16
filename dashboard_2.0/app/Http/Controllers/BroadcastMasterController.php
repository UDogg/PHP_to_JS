<?php

namespace App\Http\Controllers;
use App\Models\BroadcastMaster;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use App\Models\BroadcastStatusView;

use Illuminate\Http\Request;

class BroadcastMasterController extends Controller
{
    public function storeBroadcastData(Request $request){

        $validator = Validator::make($request->all(),[
            'broadcast_name' => 'required|string',
            'user_type' => 'required|integer',
            'category' => 'required|in:Policy Changes,Reminders,Alerts,Events,News and Updates',
            'content_type' => 'required|in:Video,Blog,Document,Content',
            'title' => 'required|string',
            'description' => 'nullable|string',
            'link' => 'nullable|string',
            'image' => 'nullable|mimes:jpeg,png,jpg,gif,svg,pdf',
            'choose_role' => 'required|integer',
            'priority' => 'required|in:High,Medium,Low',
            'from_date' => 'required|date',
            'to_date' => 'required|date',
            'status' => 'required|in:Y,N',
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }
        
        $fileUrl = null;
        if ($request->hasFile('image')) {
            $file = $request->file('image');
            $fileName = 'file_' . time() . '.' . $file->getClientOriginalExtension();
            $file->storeAs('broadCast_files', $fileName, 'public');
            $fileUrl = Storage::disk('public')->url('broadCast_files/' . $fileName);
        }
        
        $broadcastData = BroadcastMaster::create([
            'broadcast_name' => $request->input('broadcast_name'),
            'user_type' => $request->input('user_type'),
            'category' => $request->input('category'),
            'content_type' => $request->input('content_type'),
            'title' => $request->input('title'),
            'description' => $request->input('description'),
            'link' => $request->input('link'),
            'image' => $fileUrl,
            'choose_role' => $request->input('choose_role'),
            'priority' => $request->input('priority'),
            'from_date' => $request->input('from_date'),
            'to_date' => $request->input('to_date'),
            'status' => $request->input('status'),
        ]);

        return response()->json([
            'success' => true,
            'data' => $broadcastData,
            'message' => 'Data stored successfully!'
        ]);

    }

    public function updateBroadcastData(Request $request){

        $validator = Validator::make($request->all(),[
            'broadcast_name' => 'required|string',
            'user_type' => 'required|integer',
            'category' => 'required|in:Policy Changes,Reminders,Alerts,Events,News and Updates',
            'content_type' => 'required|in:Video,Blog,Document,Content',
            'title' => 'required|string',
            'description' => 'nullable|string',
            'link' => 'nullable|string',
            // 'image' => 'image|nullable|mimes:jpeg,png,jpg,gif,svg,pdf',
            'choose_role' => 'required|integer',
            'priority' => 'required|in:High,Medium,Low',
            'from_date' => 'required|date',
            'to_date' => 'required|date',
            'status' => 'required|in:Y,N',
        ]);
        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }

        $broadcastData = BroadcastMaster::find($request->id);

        if (!$broadcastData) {
            return response()->json(['message' => 'Broadcast data not found.'], 404);
        }

        $imageUrl = $broadcastData->image;

        if ($request->hasFile('image')) {
            if ($broadcastData->image) {
                Storage::disk('public')->delete('broadCast_image/' . basename($broadcastData->image));
            }

            $imageFile = $request->file('image'); 
            $imageFileName = 'image_' . time() . '.' . $imageFile->getClientOriginalExtension();
            $imageFile->storeAs('broadCast_image', $imageFileName, 'public');
            $imageUrl = Storage::disk('public')->url('broadCast_image/' . $imageFileName);
        }

        $broadcastData->update([
            'broadcast_name' => $request->broadcast_name,
            'user_type' => $request->user_type,
            'category' => $request->category,
            'content_type' => $request->content_type,
            'title' => $request->title,
            'description' => $request->description,
            'link' => $request->link,
            'image' => $imageUrl, 
            'choose_role' => $request->choose_role,
            'priority' => $request->priority,
            'from_date' => $request->from_date,
            'to_date' => $request->to_date,
            'status' => $request->status,
        ]);

        return response()->json([
            'success' => true,
            'data' => $broadcastData,
            'message' => 'Data updated successfully!'
        ]);

    }

    public function getBroadcastData(Request $request)
    {
        $query = BroadcastMaster::query();

        if ($contentType = $request->input('content_type')) {
            $query->where('content_type', $contentType);
        }

        if ($userType = $request->input('user_type')) {
            $query->where('user_type', $userType);
        }

        if ($request->input('pagination') == true) {
            $perPage = $request->input('per_page', 10);
            $currentPage = $request->input('page', 1);
            $total = $query->count();
            $lastPage = (int) ceil($total / $perPage);
            $broadcastData = $query->skip(($currentPage - 1) * $perPage)->take($perPage)->get();

            $pagination = [
                'pagination_type' => 'integrated',
                'per_page' => $perPage,
                'current_page' => $currentPage,
                'prev_page_page' => $currentPage > 1 ? $currentPage - 1 : null,
                'next_page_page' => $currentPage < $lastPage ? $currentPage + 1 : null,
                'total' => $total,
                'last_page' => $lastPage,
            ];
        } else {
            $broadcastData = $query->get();
            $pagination = null; 
        }

        // Response with data and pagination
        return response()->json([
            'success' => true,
            'column_head' => [
                [
                    "header" => "Category",
                    "accessorKey" => "category",
                    "isActions" => false,
                ],
                [
                    "header" => "Content_Type",
                    "accessorKey" => "content_type",
                    "isActions" => false,
                ],
                [
                    "header" => "User_type",
                    "accessorKey" => "user_type",
                    "isActions" => false,
                ],
                [
                    "header" => "Created_on",
                    "accessorKey" => "created_at",
                    "isActions" => false,
                ],
                [
                    "header" => "From_date",
                    "accessorKey" => "from_date",
                    "isActions" => false,
                ],
                [
                    "header" => "To_date",
                    "accessorKey" => "to_date",
                    "isActions" => false,
                ],
                [
                    "header" => "Priority",
                    "accessorKey" => "priority",
                    "isActions" => false,
                ],
                [
                    "header" => "Status",
                    "accessorKey" => "status",
                    "isActions" => false,
                ],
            ],
            'data' => $broadcastData, 
            'pagination' => $pagination,
        ]);
    }


    public function deleteBroadcastData(Request $request){
        $broadcast_data = BroadcastMaster::find( $request->id);
        $final = $broadcast_data->delete();
        if($final){
            return response()->json([
                'status' => 200,
                'return_data' => $broadcast_data,
                'message' => 'Data Deleted Successfully'
            ]);
        }
        
    }

    public function broadcastPopupList(Request $request)
    {
        $user = Auth::user();
        $userType = intval($user->usertype);
        $userRoleId = DB::table('model_has_roles')
                        ->where('model_id', $user->id)
                        ->value('role_id'); 

        if (!$userType || !$userRoleId) {
            return response()->json(['success' => false, 'message' => 'User role or type not found'], 400);
        }

        $broadcastData = BroadcastMaster::where('user_type', $userType)
                        ->where('choose_role', $userRoleId)
                        ->where('status', 'Y')
                        ->get();

        foreach ($broadcastData as $broadcast) {
            $statusRecord = BroadcastStatusView::where('user_id', $userType)
                                                ->where('broadcast_id', $broadcast->id)
                                                ->first();

            if (!$statusRecord) {
                $statusRecord = BroadcastStatusView::create([
                    'user_id' => $userType,
                    'broadcast_id' => $broadcast->id,
                    'last_shown_date' => null
                ]);
            }

            if ($broadcast->priority == 'High') {
                $broadcast->show = true;

            } elseif ($broadcast->priority == 'Low') {
                if (is_null($statusRecord->last_shown_date)) {
                    $broadcast->show = true;
                    $statusRecord->last_shown_date = now()->format('Y-m-d');
                    $statusRecord->save();
                } else {
                    $broadcast->show = false;
                }

            } elseif ($broadcast->priority == 'Medium') {
                $today = now()->format('Y-m-d');
                if ($statusRecord->last_shown_date != $today) {
                    $broadcast->show = true;
                    $statusRecord->last_shown_date = $today;
                    $statusRecord->save();
                } else {
                    $broadcast->show = false;
                }
            }
        }

        $sortedBroadcastData = $broadcastData->sortBy(function($broadcast){
            return ['High' =>1, 'Medium' => 2, 'Low' => 3][$broadcast->priority];
        })->values();

        return response()->json([
            'success' => true,
            'data' => $sortedBroadcastData,
            'message' => 'Broadcast data retrieved successfully!'
        ]);
    }
}
