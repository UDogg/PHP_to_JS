<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\Event;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;

class EventController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function __condtructor()
    {
//        $this->user = Auth::user();
//        if (!$this->user->can('event.view')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
    }
    public function index()
    {
        $event = Event::select('event_id', 'event_name', 'created_at', 'updated_at')->orderBy('event_id', 'desc')->latest();
        $columns = $event;
        $event_count = $event->get();
        $columns = $event;
        $event = $event->get();
        if (count($event_count) != 0) {
            $columns = $event;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['event_id', 'event_name', 'created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'event_id') {
                unset($columns[$key]);
            } elseif ($value === 'event_name') {
                $columns[$key] = 'Event Name';
            } elseif ($value === 'created_at') {
                $columns[$key] = 'Created At';
            } elseif ($value === 'updated_at') {
                $columns[$key] = 'Updated At';
            } else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }
        return view('event.index', compact('event', 'columns'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        return view('event.create');
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
//        if (!$this->user->can('event.edit')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        $rules = [
            'event_name' => ['required', 'string', 'unique:event'],


        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        } else {
            $event = new Event();
            $event->event_name = $request->event_name; // Store total minutes in the database

            $event->save();

            if ($event->save()) {
                return redirect()->route('event.index')->with([
                    'message' => 'Event Created Successfully.',
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
    public function show($id)
    {
        $event = Event::findOrFail($id);
        // dd($event);
        return view('event.edit', compact('event'));
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit($id)
    {
        $event = Event::findOrFail($id);
        // dd($event);
        return view('event.edit', compact('event'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, string $id)
    {
        if (!$this->user->can('event.edit')) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $rules = [
            'event_name' => ['required', 'string'], // Adjust as per your actual requirements

        ];

        // Validate the incoming request data
        $validator = Validator::make($request->all(), $rules);

        // Check if validation fails
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }

        // Find the existing SMS template by ID
        $event = Event::find($id);

        if (!$event) {
            return redirect()->back()->withErrors([
                'message' => 'Event not found.',
            ])->withInput();
        }

        // Update event template data
        $event->event_name = $request->event_name;

        // Save the updated event template
        if ($event->save()) {
            return redirect()->route('event.index')->with([
                'message' => 'Event Updated Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->back()->withErrors([
                'message' => 'Error While Updating event.',
            ])->withInput();
        }
    }

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
//        if (!$this->user->can('event.edit')) {
//            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
//        }
        $event = Event::find($id);
        if ($event->delete()) {
            return redirect()->route('event.index')->with([
                'message' => 'Event Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('event.index')->with([
                'message' => 'Error While Deleting the event.',
                'class' => 'danger',
            ]);
        }
    }
}
