<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\ZoneMasterModel;
use App\Models\VerticalMaster;

class ZoneMasterController extends Controller
{
    public function index()
    {
        $data = ZoneMasterModel::all();
        $verticalMaster = VerticalMaster::all();
        return view('zone_master', compact('data', 'verticalMaster'));
    }

    public function getData(request $request) {
        $data = ZoneMasterModel::all();
        return ([
            'status' => 200,
            'data' => $data,
            'message' => 'success'
        ]);
    }
    public function store(Request $request)
    {


        if (!empty($request)) {

            $office_zone =  $request['officeZone'] ?? '';
            $office_name =  $request['officeName'] ?? '';
            $parent_office =  $request['parentOffice'] ?? '';
            $office_pincode =  $request['officePincode'] ?? '';
            $contact_phone =  $request['contactPhone'] ?? '';
            $contact_email =  $request['contactEmail'] ?? '';
            $address =  $request['address'] ?? '';

            ZoneMasterModel::create([
                'office_zone' => $office_zone,
                'office_name' => $office_name,
                'parent_office' => $parent_office,
                'office_pincode' => $office_pincode,
                'contact_phone' => $contact_phone,
                'contact_email' => $contact_email,
                'address' => $address
            ]);
            return  response()->json(['status' => 200, 'message' => 'Zone Added Successfully']);
        } else {
            return  response()->json(['status' => 400, 'message' => 'Zone Added Failed']);
        }
    }
    public function edit(int $id)
    {
        $data = ZoneMasterModel::find($id);

        if (!$data) {
            return response()->json([
                'status' => 404,
                'message' => 'No Data Found'
            ], 404);
        }

        return response()->json([
            'status' => 200,
            'data' => $data
        ]);
    }

    public function update(Request $request)
    {
        // Find the record
        $data = ZoneMasterModel::find($request->id);

        // Check if the record exists
        if (!$data) {
            return response()->json([
                'error' => 'Record not found'
            ], 404);
        }

        // Update fields
        $data->office_zone = $request->off_zone;
        $data->office_name = $request->off_name;
        $data->parent_office = $request->parent_office;
        $data->office_pincode = $request->office_pincode;
        $data->contact_phone = $request->contact_phone;
        $data->contact_email = $request->contact_email;
        $data->address = $request->address;
        $data->save();

        return response()->json(['success' => 'Data updated successfully']);
    }

    public function delete(Request $request)
    {
        if (!auth()->check()) {
            return response()->json(['error' => 'User not authenticated'], 401);
        }
    
        $data = ZoneMasterModel::find($request->id);
        
        if (!$data) {
            return response()->json(['error' => 'Data not found'], 404);
        }
    
        $data->delete();
    
        return response()->json(['success' => 'Data deleted successfully']);
    }

    public function vertical(Request $request)
    {
        if (!empty($request)) {
            VerticalMaster::create([
                'vertical_name' => $request['verticalName'],
                'created_by' => auth()->user()['email']
            ]);
            return  response()->json(['status' => 200, 'message' => 'vertical Added Successfully']);
        } else {
            return  response()->json(['status' => 400, 'message' => 'vertical Added Failed']);
        }
    }

    public function vertical_delete(request $request)
    {
        $data = VerticalMaster::find($request->id);
        $data->delete();

        return response()->json(['success' => 'Data deleted successfully']);
    }
    public function vertical_update(Request $request)
    {
        $data = VerticalMaster::find($request->id);
        $data->vertical_name = $request->name;
        $data->save();

        return response()->json(['success' => 'Data updated successfully']);
    }
}
