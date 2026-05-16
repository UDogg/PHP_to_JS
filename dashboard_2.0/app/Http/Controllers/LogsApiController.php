<?php

namespace App\Http\Controllers;

use App\Models\LogsApi;
use Illuminate\Http\Request;

class LogsApiController extends Controller
{
    public function LogsApiList(Request $request)
    {
        $query = LogsApi::query();

        if ($request->has('search')) {
            $search = $request->input('search');
            $query->where('url', 'like', "%{$search}%")
                ->orWhere('method', 'like', "%{$search}%")
                ->orWhere('headers', 'like', "%{$search}%")
                ->orWhere('request', 'like', "%{$search}%")
                ->orWhere('response', 'like', "%{$search}%")
                ->orWhere('api_type', 'like', "%{$search}%");
        }

        $logs = $query->orderBy('created_at', 'desc')->paginate(10);

        if ($request->ajax()) {
            return response()->json([
                'data' => $logs->items(),
                'pagination' => [
                    'total_records' => $logs->total(), 
                    'per_page' => $logs->perPage(),   
                    'current_page' => $logs->currentPage(),
                    'total_pages' => $logs->lastPage(),     
                    'next_page_url' => $logs->nextPageUrl(), 
                    'prev_page_url' => $logs->previousPageUrl(), 
                    'last_page_url' => $logs->url($logs->lastPage()), 
                ],
            ]);
        }
        return view('logs_api', compact('logs'));
    }
}
