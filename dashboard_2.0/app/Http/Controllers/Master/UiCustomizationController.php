<?php

namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;
use App\Models\UiCustomization;
use Illuminate\Http\Request;
use Illuminate\Support\Str;
use App\Models\Broker;
use Illuminate\Support\Facades\Validator;

class UiCustomizationController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        $placeholder = UiCustomization::select('placeholder_id', 'username','password','broker_name','created_at', 'updated_at')->orderBy('placeholder_id','desc')->latest();
        $columns = $placeholder;
        $placeholder_count = $placeholder->get();
        $columns = $placeholder;
        $placeholder = $placeholder->get();
        if(count($placeholder_count) != 0) {
            $columns = $placeholder;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['placeholder_id', 'username','password','broker_name','created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'placeholder_id') {
                unset($columns[$key]);
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
        return view('placeholder.index', compact('placeholder', 'columns'));
    }
    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        $brokerNames = Broker::pluck('broker_name');
        return view('placeholder.create', compact('brokerNames'));
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        $uiCustomization = UiCustomization::first();
        $username = $uiCustomization ? $uiCustomization->username : '';
        $password = $uiCustomization ? $uiCustomization->password : '';

    // Store the username in the session
        session(['username_placeholder' => $username]);
        $rules = [
            'username' => ['required', 'string'],
            'password' => ['required', 'string'],
            'broker_name' => ['required', 'string'],

        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{
            $placeholder = new UiCustomization();
            $placeholder->username = $request->username;
            $placeholder->password = $request->password;
            $placeholder->broker_name = $request->broker_name;
            $placeholder->save();
            if ($placeholder->save()==true) {
                return redirect()->route('placeholder.index')->with([
                    'message' => 'placeholder Created Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating User.',
                ])->withInput()->with('username_placeholder', $username, 'password_placeholder', $password);
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
    public function edit(UiCustomization $placeholder)
    {
        $brokerNames = Broker::pluck('broker_name');
        return view('placeholder.edit', compact('placeholder', 'brokerNames'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, UiCustomization $placeholder)
    {
        $rules = [
            'username' => ['required', 'string'],
            'password' => ['required', 'string'],
            'broker_name' => ['required', 'string'],

        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{

            $placeholder->username = $request->username;
            $placeholder->password = $request->password;
            $placeholder->broker_name = $request->broker_name;
            $placeholder->save();
            if ($placeholder->save()==true) {
                return redirect()->route('placeholder.index')->with([
                    'message' => 'placeholder Created Successfully.',
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
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        $placeholder = UiCustomization::find($id);
        if ($placeholder->delete()) {
            return redirect()->route('placeholder.index')->with([
                'message' => 'placeholder Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('placeholder.index')->with([
                'message' => 'Error While Deleting the placeholder.',
                'class' => 'danger',
            ]);
        }
    }
}
