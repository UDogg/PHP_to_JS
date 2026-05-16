<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\email_template;

class EmailtemplateController extends Controller
{
    //
    function show(Request $request){
        $result  = email_template::paginate(5);
        return view('EmailtemplateAddview',['EmailViews'=>$result]);
    }


    function add(Request $request){
        return view('EmailtemplateView');
    }


    function store(Request $request){
        $result = new email_template();
        $result->stage = $request->stage;
        $result->subject = $request->subject;
        $result->body = $request->body;
        $result->save();
        // $alldata = email_template::all();
        return Redirect()->route('Email-Template-Index');
        // return view('EmailtemplateAddview',["EmailViews"=>$alldata]);
    }

    function  delete($id){
        email_template::destroy($id);
        // $alldata = email_template::all();
        return redirect()->route('Email-Template-Index');
        // return view('EmailtemplateAddview',["EmailViews"=>$alldata]);
    }

    function updatepage($id){
        $result = email_template::findOrFail($id);
        return view('EmailtemplateUpdateview',["EmailUpdateview"=>$result]);
    }
    
    function storeUpdate(Request $request,$id){
        $result = email_template::findOrFail($id);
        $result->stage = $request->stage;
        $result->subject = $request->subject;
        $result->body = $request->body;
        $result->save();
        return redirect()->route('Email-Template-Index');
    }

    function search(Request $request){

        $result = email_template::where('stage','like',"%".$request->search."%")->paginate(5);

        // if($request->filled('search')){
        //     $search = $request->search;
        //     $query->where(function ($q) use ($search){
        //         $q->whereor('stage','like',"%".$search."%")
        //         ->whereor('subject','like',"%".$search."%");
        //         // ->whereor('body','like',"%".$search."%");
        //     });
        // }

        // $result = $query->paginate(5);
        // // $result  = email_template::all();
        return view('EmailtemplateAddview',['EmailViews'=>$result]);
        // // return "vivek";
        // echo  "vivem";
    }

}
