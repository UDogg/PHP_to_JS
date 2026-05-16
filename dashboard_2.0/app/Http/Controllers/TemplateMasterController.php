<?php

namespace App\Http\Controllers;

use App\Mail\CommunicationMail;
use App\Models\EmailType;
use App\Models\Event;
use App\Models\TemplateModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Mail;
use Illuminate\Support\Facades\Validator;

class TemplateMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function index()
    {
        $templates = TemplateModel::orderBy('template_id','desc')->get();
        return view('template_master.index', compact('templates'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        $event = Event::pluck('event_name');

        return view('template_master.create', compact('event'));
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {

        $rules = [
            'title'=>'required|string|max:150',
            'communication_type'=>'required|in:email,sms,whatsapp',
            'status'=>'required'
        ];

        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return back()->withErrors($validator)->withInput();

        } else {
            $template = TemplateModel::create([
                "title" => $request->title,
                "dlt_id" => $request->dlt_id,
                "communication_type" => $request->communication_type,
                "event" => $request->input('event'),
                "content" => $request->input('content'),
                "status" => $request->status,
            ]);

            if ($template->save()) {
                            return response()->json([
                                'status' => 200,
                                'return_data' => $template,
                                'message' => 'Template Added Successfully',
                            ], 200);
                        } else {
                            return response()->json(
                                [
                                    'status' => 500,
                                    'return_data' => $template,
                                    'message' => 'Failed to add template',
                                ],
                                500
                            );
                        }
        }
    }

    /**
     * Display the specified resource.
     */
    public function show($id)

    {
       $template = TemplateModel::findOrFail($id);
        return view('template_master.show' , compact('template'));

    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(TemplateModel $template)
    {
        $event = Event::pluck('event_name');


        return view('template_master.edit', compact('template', 'event'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, TemplateModel $template)
    {
        $rules = [
            'title' => 'required|string|max:150',
            'communication_type' => 'required|in:email,sms,whatsapp',
            'content' => 'required',
        ];


        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Validation fails',
                    'errors' => $validator->errors(),
                ],
                500
            );
        } else {

            $status = TemplateModel::findOrFail($request->id);

            if ($status) {
                $status->update($request->all());

                return response()->json(
                    [
                        'status' => 200,
                        'return_data' => $status,
                        'message' => 'Status Updated Successfully',
                    ],
                    200
                );
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Status not found',
                    ],
                    500
                );
            }
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(Request $request)
    {
        $templateData = TemplateModel::where('template_id', $request->template_id)->first();

        if ($templateData) {

            $templateData->delete();
            return response()->json(['message' => 'Template deleted successfully']);
        } else {

            return response()->json(['message' => 'Template not found or already deleted']);
        }


    }

    public function sendEmail(Request $request)
    {
        $request->validate([
            'email' => 'required|email',
            'title' => 'required|string',
            'content' => 'required|string',
        ]);

        $details = [
            'title' => $request->title,
            'content' => $request->content,
        ];

        Mail::to($request->email)->send(new CommunicationMail($details));

        return back()->with('success', 'Email sent successfully!');
    }

}
