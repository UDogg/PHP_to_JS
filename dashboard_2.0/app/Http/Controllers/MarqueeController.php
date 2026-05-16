<?php

namespace App\Http\Controllers;

use App\Models\Marquee;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class MarqueeController extends Controller
{

    public function index()
    {
        $datas = Marquee::all();
        return view('marquee.index' , compact('datas'));
    }

    public function create()
    {
        return view("marquee.create");
    }

    public function store(Request $request)
    {
        $rules = [
            'usertype' => 'required|string|max:255',
            'status' => 'required|in:Y,N',
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{
            $data = new Marquee();
            $data->usertype = $request->usertype;
            $data->status = $request->status;
            $data->save();
            if ($data->save()==true) {
                return redirect()->route('marquee.index')->with([
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

    public function edit(Marquee $marquee)
    {
        $data = $marquee;
        return view('marquee.edit' , compact('data'));
    }


    public function update(Request $request, Marquee $marquee)
    {
        $marquee->usertype = $request->usertype;
        $marquee->status = $request->status;
        $marquee->save();
        if ($marquee->save()==true) {
            return redirect()->route('marquee.index')->with([
                'message' => 'scrolling Updated Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->back()->withErrors([
                'message' => 'Error While Updating.',
            ])->withInput();
        }
    }

    public function destroy($id)
    {
        $broker = Marquee::find($id);
        if ($broker->delete()) {
            return redirect()->route('marquee.index')->with([
                'message' => 'data Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('marquee.index')->with([
                'message' => 'Error While Deleting the data.',
                'class' => 'danger',
            ]);
        }
    }
}
