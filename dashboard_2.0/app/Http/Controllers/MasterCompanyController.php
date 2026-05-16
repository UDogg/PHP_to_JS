<?php

namespace App\Http\Controllers;
use Illuminate\Http\Request;
use App\Models\masterCompany;

use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Facades\Validator;
use App\Imports\AuHierarchyDumpImport;
use Maatwebsite\Excel\Facades\Excel;

class MasterCompanyController extends Controller
{
    public function index(Request $request)
    {

        $company_data = masterCompany::orderBy('company_id', 'desc')->get();

        return view('company_master', compact('company_data'));

    }

    public function store(Request $request)
    {
        $rules = [
            'lobname' => ['required'],
            'company_name' => ['required', 'string'],
            'company_shortname' => ['nullable', 'string'],
            'logo' => 'nullable|mimes:jpeg,png,jpg|max:2048',
            'live_insu_company' => ['required', 'in:Y,N'],
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Invalid request data',
                'errors' => $validator->errors()
            ], 500);
        }

        $logoPath = null;

        if ($request->hasFile('logo')) {
            $logoFile = $request->file('logo');
            $logoFileName = 'logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
            $logoPath = $logoFile->storeAs('broker_logo', $logoFileName, 'public');
        }

        try {
            $company_data = new masterCompany();
            $company_data->lobname = $request->lobname;
            $company_data->company_name = $request->company_name;
            $company_data->company_shortname = $request->company_shortname;
            $company_data->logo = $logoPath;
            $company_data->live_insu_company = $request->live_insu_company;
            $company_data->save();

            return response()->json([
                'status' => 200,
                'return_data' => $company_data,
                'message' => 'Company Master Created Successfully',
            ]);
        } catch (\Exception $e) {
            return response()->json([
                'status' => 500,
                'return_data' => [],
                'message' => 'Server Error: ' . $e->getMessage(),
            ]);
        }
    }

    public function update(Request $request)
    {
        $rules = [
            'lobname' => ['required'],
            'company_name' => ['required', 'string'],
            'company_shortname' => ['nullable', 'string'],
            'logo' => ['nullable', 'mimes:jpeg,png,jpg', 'max:2048'],
            'live_insu_company' => ['required', 'in:Y,N'],
        ];
    
        $validator = Validator::make($request->all(), $rules);
    
        if ($validator->fails()) {
            return response()->json([
                'status' => 500,
                'message' => 'Validation failed',
                'errors' => $validator->errors(),
            ], 500);
        }
    
        $company_data = masterCompany::find($request->id);
    
        if (!$company_data) {
            return response()->json([
                'status' => 404,
                'message' => 'Company not found',
            ], 404);
        }
    
        if ($request->has('remove_logo') && $request->remove_logo == 1) {
            $company_data->logo = null;
        } elseif ($request->hasFile('logo')) {
            $logoFile = $request->file('logo');
            $logoFileName = 'logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
            $logoPath = $logoFile->storeAs('broker_logo', $logoFileName, 'public');
            $company_data->logo = $logoPath;
        }
    
        $company_data->lobname = $request->lobname;
        $company_data->company_name = $request->company_name;
        $company_data->company_shortname = $request->company_shortname;
        $company_data->live_insu_company = $request->live_insu_company;
    
        $company_data->save();
    
        return response()->json([
            'status' => 200,
            'message' => 'Company updated successfully',
            'return_data' => $company_data,
        ]);
    }
    


    public function destroy(Request $request)
    {

        $company_data = masterCompany::where('company_id', $request->company_id)->first();

        if ($company_data) {

            $company_data->delete();
            return response()->json(['message' => 'Company Data deleted successfully']);
        } else {

            return response()->json(['message' => 'Company Data not found or already deleted']);
        }
    }

    public function show(request $request)
    {
       $company_data = masterCompany::select('company_id', 'lobname', 'company_name','company_shortname','logo','live_insu_company' )->get();

        return response()->json($company_data);

    }

    public function masterCompanies()
    {
        $companies = masterCompany::select('company_id', 'lobname', 'company_name', 'company_shortname', 'logo', 'live_insu_company')
            ->where('live_insu_company', 'Y')
            ->orderBy('company_id', 'desc')
            ->get()
            ->map(function ($company) {
                $company->logo_url = $company->logo ? asset(Storage::url($company->logo)) : null;
                return $company;
            });

        return response()->json([
            'status' => 200,
            'message' => 'Company list fetched successfully',
            'data' => $companies
        ], 200);
    }

    public function ImportAuHierarchyDump(Request $request)
    {
        $request->validate([
            'file' => 'required|mimes:xlsx,xls,csv'
        ]);
        Excel::import(new AuHierarchyDumpImport, $request->file('file'));

        return response()->json([
            'status' => true,
            'message' => 'AU hierarchy data imported successfully'
        ]);
    }

}
