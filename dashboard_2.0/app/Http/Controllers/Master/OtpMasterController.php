<?php

namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;

use App\Models\OtpMaster;
use App\Models\Broker;
use Illuminate\Http\Request;
use Illuminate\Support\Str;
use Illuminate\Support\Facades\Validator;

class OtpMasterController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function __condtructor()
    {
        $this->user = Auth::user();
        if(!$this->user->can('otp.view'))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
    }
    public function index()
    {
        $otpData = OtpMaster::select('otp_id', 'otp_validation_time','resend_otp_time','broker_name','created_at', 'updated_at')->orderBy('otp_id','desc')->latest();
        $columns = $otpData;
        $otpData_count = $otpData->get();
        $columns = $otpData;
        $otpData = $otpData->get();
        if(count($otpData_count) != 0) {
            $columns = $otpData;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['otp_id', 'otp_validation_time','resend_otp_time','broker_name','created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'otp_id') {
                unset($columns[$key]);
            } elseif ($value === 'otp_validation_time') {
                $columns[$key] = 'OTP Validation Time';
            } elseif ($value === 'resend_otp_time') {
                $columns[$key] = 'Resend OTP Time';
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
        return view('otp.index', compact('otpData', 'columns'));
    }

    public function create()
    {
        $otpData = Broker::pluck('broker_name');
        return view('otp.create', compact('otpData'));
    }

    public function store(Request $request)
    {
        $rules = [
            'otp_validation_time' => ['required', 'regex:/^\d{2}:\d{2}:\d{2}$/'], 
            'resend_otp_time' => ['required', 'regex:/^\d{2}:\d{2}:\d{2}$/'], 
            'broker_name' => ['required', 'string'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        } 

        $otpData = new OtpMaster();
        $otpData->otp_validation_time = $request->otp_validation_time;
        $otpData->resend_otp_time = $request->resend_otp_time;
        $otpData->broker_name = $request->broker_name;
        $otpData->save();

        return redirect()->route('otp.index')->with('message', 'OTP Created Successfully.');
    }

    

    public function show(string $id)
    {
        //
    }

    public function edit(string $id)
    {
        $otpData = OtpMaster::findOrFail($id);
        return view('otp.edit', compact('otpData'));
    }

    public function update(Request $request, $id)
    {
    
        $rules = [
            'otp_validation_time' => ['required', 'regex:/^\d{2}:\d{2}:\d{2}$/'], 
            'resend_otp_time' => ['required', 'regex:/^\d{2}:\d{2}:\d{2}$/'], 
            'broker_name' => ['required', 'string'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }

        // Find OTP entry
        $otpData = OtpMaster::findOrFail($id);

        // Save HH:MM:SS format correctly
        $otpData->update([
            'otp_validation_time' => $request->otp_validation_time,
            'resend_otp_time' => $request->resend_otp_time,
            'broker_name' => $request->broker_name
        ]);

        return redirect()->route('otp.index')->with('message', 'OTP Updated Successfully.');
    }

    

    private function convertMinutesToTime($minutes)
    {
        $hours = floor($minutes / 60);
        $minutes = $minutes % 60;
        return sprintf('%02d:%02d:00', $hours, $minutes);
    }

    public function destroy(string $id)
    {
        // if (!$this->user->can('otp.edit')) {
        //     return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        // }
        $otpData = OtpMaster::find($id);
        if ($otpData->delete()) {
            return redirect()->route('otp.index')->with([
                'message' => 'OTP Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('otp.index')->with([
                'message' => 'Error While Deleting the OTP.',
                'class' => 'danger',
            ]);
        }
    }
}
