<?php

namespace App\Http\Controllers;
use App\Models\SmsActivityLog;
use Illuminate\Support\Str;
use Illuminate\Http\Request;

class SmsActivityLogController extends Controller
{
    public function index()
    {
        $logs = SmsActivityLog::select('id', 'mobile','message','type','status','sent_at','created_at')->orderBy('created_at','desc');

        $logs_count = $logs->get();

        $columns = $logs;
        $logs = $logs->paginate(10);
        $count = $logs->lastPage();

        $column_array = [];
        if(count($logs_count) != 0) {
            $columns = $logs;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['id', 'mobile','message','type','status','sent_at','created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'id') {
                unset($columns[$key]);

            } elseif ($value === 'mobile') {
                $columns[$key] = 'Mobile';
            } elseif ($value === 'message') {
                $columns[$key] = 'Message';
            // } elseif ($value === 'body') {
            //     $columns[$key] = 'Body';
            } elseif ($value === 'type') {
                $columns[$key] = 'Type';
            } elseif ($value === 'status') {
                $columns[$key] = 'Status';
            } elseif ($value === 'sent_at') {
                $columns[$key] = 'Sent At';
            } elseif ($value === 'created_at') {
                $columns[$key] = 'Created At';
            } elseif ($value === 'updated_at') {
                $columns[$key] = 'Updated At';
            } else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }
        return view('sms_logs', compact('logs', 'columns','count'));


    }
}
