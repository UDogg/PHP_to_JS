<?php

namespace App\Http\Controllers;

use App\Exports\SmsActivityLogsExport;
use App\Models\SmsActivityLog;
use Illuminate\Http\Request;
use Maatwebsite\Excel\Facades\Excel;

class SmsActivityLogControllerNew extends Controller
{
    public function index(Request $request)
    {
        $query = SmsActivityLog::query();

        if ($request->filled('search')) {
            $search = $request->search;
            $query->where(function ($q) use ($search) {
                $q->where('mobile', 'like', "%$search%")
                  ->orWhere('message', 'like', "%$search%")
                  ->orWhere('type', 'like', "%$search%")
                  ->orWhere('status', 'like', "%$search%")
                  ->orWhere('sent_at', 'like', "%$search%")
                  ->orWhere('user_id', 'like', "%$search%");

                  
            });
        }

        $logs = $query->orderBy('created_at', 'desc')->paginate(10);

        return view('sms_activity_logs.index', compact('logs'));
    }

    public function create()
    {
        return view('sms_activity_logs.create');
    }

    public function store(Request $request)
    {
        $request->validate([
            'mobile' => 'required|integer',
            'message' => 'required|string',
            'type' => 'required|string',
            'status' => 'required|string',
            'sent_at' => 'required|string',
            'user_id' => 'required|integer',
        ]);

        SmsActivityLog::create([
            'mobile'   => $request->mobile,
            'message'  => $request->message,
            'type'     => $request->type,
            'status'   => $request->status,
            'sent_at'  => $request->sent_at,
            'user_id'  => $request->user_id,
        ]);

        return redirect()->route('smsActivityLog.index')->with('success', 'Log created successfully.');
    }

    public function smsEdit(Request $request, $id)
    {
        $log = SmsActivityLog::findOrFail($id);
        return view('sms_activity_logs.edit', compact('log'));
    }

    public function smsUpdate(Request $request, $id)
    {
        $request->validate([
            'mobile' => 'required|integer',
            'message' => 'required|string',
            'type' => 'required|string',
            'status' => 'required|string',
            'sent_at' => 'required|string',
            'user_id' => 'required|integer',
        ]);

        $log = SmsActivityLog::findOrFail($id);
        $log->update([
            'mobile'   => $request->mobile,
            'message'  => $request->message,
            'type'     => $request->type,
            'status'   => $request->status,
            'sent_at'  => $request->sent_at,
            'user_id'  => $request->user_id,
        ]);
        return redirect()->route('smsActivityLog.index')->with('success', 'Log updated successfully.');
    }

    public function delete(Request $request, $id)
    {
        $log = SmsActivityLog::findOrFail($id);
        $log->delete();

        return redirect()->route('smsActivityLog.index')->with('success', 'Log deleted successfully.');
    }

    public function export()
    {
        return Excel::download(new SmsActivityLogsExport, 'sms_activity_logs.xlsx');
    }


}
