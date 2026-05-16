<?php

namespace App\Http\Controllers;

use App\Models\SmsTemplate;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;

class SmsTemplateController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function __construct()
    {
//        $this->user = Auth::user();
//        if (!$this->user->can('sms_template.view')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
    }
    public function index()
    {
        $sms = SmsTemplate::select('template_id', 'title', 'content', 'status','dlt_id', 'created_at', 'updated_at')->orderBy('template_id', 'desc')->latest();
        $columns = $sms;
        $sms_count = $sms->get();
        $columns = $sms;
        $sms = $sms->get();
        if (count($sms_count) != 0) {
            $columns = $sms;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['template_id', 'title', 'content', 'status', 'dlt_id', 'created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'template_id') {
                unset($columns[$key]);
            } elseif ($value === 'title') {
                $columns[$key] = 'Title';

            } elseif ($value === 'content') {
                $columns[$key] = 'Content';
            } elseif ($value === 'status') {
                $columns[$key] = 'Status';
            } elseif ($value === 'created_at') {
            } elseif ($value === 'dlt_id') {
                $columns[$key] = 'dlt_id';
            } elseif ($value === 'created_at') {
                $columns[$key] = 'Created At';
            } elseif ($value === 'updated_at') {
                $columns[$key] = 'Updated At';
            } else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }
        return view('sms_template.index', compact('sms', 'columns'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        $sms = SmsTemplate::all();
        return view('sms_template.create', compact('sms'));
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {

//        if (!$this->user->can('sms_template.edit')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        $rules = [
            'title' => ['required', 'string'], // Validate as integer and ensure it's positive
            'content' => ['required', 'string'], // Adjust as per your actual requirements
            'status' => ['required'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        } else {
            $sms = new SmsTemplate();
            $sms->title = $request->title; // Store total minutes in the database
            $sms->content = $request->content;
            $sms->status = $request->status;
            $sms->dlt_id = $request->dlt_id;
            $sms->save();

            if ($sms->save()) {
                return redirect()->route('sms_template.index')->with([
                    'message' => 'SMS Template Created Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating OTP.',
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
    public function edit($id)
    {
        $sms = SmsTemplate::findOrFail($id);
        // dd($sms);
        return view('sms_template.edit', compact('sms'));
    }

    /**
     * Update the specified resource in storage.
     */

    public function update(Request $request, $id)
    {

//        if (!$this->user->can('sms_template.edit')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        // Define validation rules
        $rules = [
            'title' => ['required', 'string'], // Adjust as per your actual requirements
            'content' => ['required', 'string'], // Adjust as per your actual requirements
            'status' => ['required'],
        ];

        // Validate the incoming request data
        $validator = Validator::make($request->all(), $rules);

        // Check if validation fails
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }

        // Find the existing SMS template by ID
        $sms = SmsTemplate::find($id);

        if (!$sms) {
            return redirect()->back()->withErrors([
                'message' => 'SMS Template not found.',
            ])->withInput();
        }

        // Update SMS template data
        $sms->title = $request->title;
        $sms->content = $request->content;
        $sms->status = $request->status;
        $sms->dlt_id = $request->dlt_id;

        // Save the updated SMS template
        if ($sms->save()) {
            return redirect()->route('sms_template.index')->with([
                'message' => 'SMS Template Updated Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->back()->withErrors([
                'message' => 'Error While Updating SMS Template.',
            ])->withInput();
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
//        if (!$this->user->can('sms_template.edit')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        $sms = SmsTemplate::find($id);
        if ($sms->delete()) {
            return redirect()->route('sms_template.index')->with([
                'message' => 'SMS Template Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('otp.index')->with([
                'message' => 'Error While Deleting the SMS Template.',
                'class' => 'danger',
            ]);
        }
    }
}
