<?php

namespace App\Http\Controllers;
use App\Models\VideoBlogsMaster;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;

use Illuminate\Http\Request;

class VideoBlogsMasterController extends Controller
{
    public function storeVideoBlogData(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'user_type' => 'required|integer',
            'content_type' => 'required|in:video,blog',
            'title' => 'required|string|max:255',
            'description' => 'required|string',
            'image' => 'image|mimes:jpeg,png,jpg,gif,svg', 
            'link' => 'required|string|url',
            'status' => 'required|in:N,Y',
            'role_id' => 'required|integer',
        ]);
        
        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }
        $imageUrl = null;
        
        if ($request->hasFile('image')) {
            $imageFile = $request->file('image'); 
            $imageFileName = 'image_' . time() . '.' . $imageFile->getClientOriginalExtension();
            $imageFile->storeAs('videoBlog_image', $imageFileName, 'public');
            $imageUrl = Storage::disk('public')->url('videoBlog_image/' . $imageFileName);
        }
        $videoBlog = VideoBlogsMaster::create([
            'user_type' => $request->input('user_type'),
            'content_type' => $request->input('content_type'),
            'title' => $request->input('title'),
            'description' => $request->input('description'),
            'image' => $imageUrl ?? null,  
            'link' => $request->input('link'),
            'status' => $request->input('status'),
            'role_id' => $request->input('role_id'),
        ]);

        return response()->json([
            'success' => true,
            'data' => $videoBlog
        ]);
    }

    public function updateVideoBlogData(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'user_type' => 'required|integer',
            'content_type' => 'required|in:video,blog',
            'title' => 'required|string|max:255',
            'description' => 'required|string',
            'image' => 'image|mimes:jpeg,png,jpg,gif,svg',
            'link' => 'required|string|url',
            'status' => 'required|in:N,Y',
            'role_id' => 'required|integer',
        ]);

        if ($validator->fails()) {
            return response()->json(['errors' => $validator->errors()], 400);
        }

        $videoBlog = VideoBlogsMaster::find($request->id);

        $imageUrl = $videoBlog->image;  
        if ($request->hasFile('image')) {
            if ($videoBlog->image) {
                Storage::disk('public')->delete('videoBlog_image/' . basename($videoBlog->image));
            }

            $imageFile = $request->file('image'); 
            $imageFileName = 'image_' . time() . '.' . $imageFile->getClientOriginalExtension();
            $imageFile->storeAs('videoBlog_image', $imageFileName, 'public');
            $imageUrl = Storage::disk('public')->url('videoBlog_image/' . $imageFileName);
        }

        $videoBlog->update([
            'user_type' => $request->user_type,
            'content_type' => $request->content_type,
            'title' => $request->title,
            'description' => $request->description,
            'image' => $imageUrl ?? null,  
            'link' => $request->link,
            'status' => $request->status,
            'role_id' => $request->role_id,
        ]);
        return response()->json([
            'success' => true,
            'data' => $videoBlog,
            'message' => 'Data updated successfully!'
        ]);
    }

    public function getVideoBlogData(Request $request)
    {
        $query = VideoBlogsMaster::query();

        if ($request->input('content_type') == 'blog') {
            $query->where('content_type', 'blog');
        }
        if ($request->input('content_type') == 'video') {
            $query->where('content_type', 'video');
        }
        if ($userType = $request->input('user_type')) {
            $query->where('user_type', $userType);
        }
    
        $video_blog_data = $query->get();
    
        return response()->json($video_blog_data);
    }

    public function deleteVideoBlogData(Request $request){
        $videoBlogData = VideoBlogsMaster::find( $request->id);
        $final = $videoBlogData->delete();
        if($final){
            return response()->json([
                'status' => 200,
                'return_data' => $videoBlogData,
                'message' => 'Data Deleted Successfully'
            ]);
        }
        
    }

}
