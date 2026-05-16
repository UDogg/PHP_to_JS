<?php

namespace App\Http\Controllers;
use App\Models\EmailActivityLog;
use Illuminate\Support\Str;

use Illuminate\Http\Request;

class EmailActivityLogController extends Controller
{
    public function index()
    {

        $logs = EmailActivityLog::select('email_id', 'email','subject','type','status','sent_at','created_at')->orderBy('created_at','desc');

        $logs_count = $logs->get();
        $columns = $logs;

        $logs = $logs->paginate(10);

        $count = $logs->lastPage();



        $column_array = [];
        if(count($logs_count) != 0) {
            $columns = $logs->all();

           $columns =  array_keys($columns[0]->toArray());


        } else {
            $columns = ['email_id', 'email','subject','type','status','sent_at','created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value == 'email_id') {
                unset($columns[$key]);

            } elseif ($value === 'email') {
                $columns[$key] = 'Email';
            } elseif ($value === 'subject') {
                $columns[$key] = 'Subject';
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
        // dd($logs);
        return view('email_logs.index', compact('logs', 'columns','count'));


    }
    public function show(Request $request)
    {
       $query = EmailActivityLog::query();
       $logs = $query->paginate(10);
        return view('email_logs.show', compact('logs'));
    }
}
