<?php

namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;
use Illuminate\Http\Request;
use App\Models\SessionTime;
use App\Models\Broker;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Validator;


class SessionTimeController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        $session = SessionTime::select('session_id', 'session_time','session_content','broker_name','created_at', 'updated_at')->orderBy('session_id','desc')->latest();
        $columns = $session;
        $session_count = $session->get();
        $columns = $session;
        $session = $session->get();
        if(count($session_count) != 0) {
            $columns = $session;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['session_id', 'session_time','session_content','broker_name','created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'session_id') {
                unset($columns[$key]);
            } elseif ($value === 'session_time') {
                $columns[$key] = 'Session Time';
            } elseif ($value === 'session_content') {
                $columns[$key] = 'Session Content';
            } elseif ($value === 'broker_name') {
                $columns[$key] = 'Broker Name';
            } elseif ($value === 'created_at') {
                $columns[$key] = 'Created At';
            } elseif ($value === 'updated_at') {
                $columns[$key] = 'Updated At';
            } else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }
        return view('session.index', compact('session', 'columns'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        $brokerNames = Broker::pluck('broker_name');
        return view('session.create', compact('brokerNames'));
    }
    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $rules = [
            'session_time' => ['required', 'string'],
            'session_content' => ['required', 'string'],
            'broker_name' => ['required', 'string'],

        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{
            $session = new SessionTime();
            $session->session_time = $request->session_time;
            $session->session_content = $request->session_content;
            $session->broker_name = $request->broker_name;
            $session->save();
            if ($session->save()==true) {
                return redirect()->route('session.index')->with([
                    'message' => 'Session Created Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating User.',
                ])->withInput();
            }
        }
    }

    /**
     * Display the specified resource.
     */
    public function show(string $id)
    {
        //
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(SessionTime $session)
    {
        $brokerNames = Broker::pluck('broker_name');
        return view('session.edit', compact('session', 'brokerNames'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, SessionTime $session)
    {
        $rules = [
            'session_time' => ['required', 'string'],
            'session_content' => ['required', 'string'],
            'broker_name' => ['required', 'string'],

        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{

            $session->session_time = $request->session_time;
            $session->session_content = $request->session_content;
            $session->broker_name = $request->broker_name;
            $session->save();
            if ($session->save()==true) {
                return redirect()->route('session.index')->with([
                    'message' => 'Session Updated Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating Session.',
                ])->withInput();
            }
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $menu = SessionTime::find($id);
        if ($menu->delete()) {
            return redirect()->route('session.index')->with([
                'message' => 'Session Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('session.index')->with([
                'message' => 'Error While Deleting the Session.',
                'class' => 'danger',
            ]);
        }
    }
}
