<?php


namespace App\Http\Controllers;
use Exception;
use App\Models\lobMaster;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;

class lobDataController extends Controller
{
    public static function index()
    {
        // $lobs = lobMaster::get()->all();
        $lobs = lobMaster::where('is_enabled', 'Y')->get();

        return view('lob_data', compact('lobs'));
    }

    public function store(Request $request)
    {
        $rules = [
            'lob_name' => ['required', 'string'],
            'lob' => ['required', 'string'],
            'is_enabled' => ['required', 'string'], 
            'frontend_url' => ['required', 'string'],
            // 'customer_frontend_url' => 'nullable|string|max:255',
            'lob_icon' => 'required|mimes:jpeg,png,jpg|max:2048',
            'lob_master_name' => ['required', 'string'],
            // 'payment_url' => 'nullable', 'string',
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json([
                'status' => 422,
                'errors' => $validator->errors(),
                'message' => 'Invalid request data',
            ], 422);
        }

        try {
            if ($request->hasFile('lob_icon')) {
                $logoFile = $request->file('lob_icon');
                $logoFileName = 'logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
                $logoPath = $logoFile->storeAs('broker_logo', $logoFileName, 'public');
            } else {
                return response()->json([
                    'status' => 400,
                    'message' => 'LOB icon file is missing or invalid.',
                ], 400);
            }

            $lobs = new lobMaster();
            $lobs->lob_name = $request->lob_name;
            $lobs->lob = $request->lob;
            $lobs->is_enabled = $request->is_enabled;
            $lobs->frontend_url = $request->frontend_url;
            $lobs->customer_frontend_url = $request->customer_frontend_url;
            $lobs->lob_icon = $logoPath;
            $lobs->lob_master_name = $request->lob_master_name;
            $lobs->payment_url = $request->payment_url;

            $lobs->save();

            return response()->json([
                'status' => 200,
                'return_data' => $lobs,
                'message' => 'LOB Data Created Successfully',
            ], 200);

        } catch (Exception $e) {
            return response()->json([
                'status' => 500,
                'message' => 'An error occurred while saving data.',
                'error' => $e->getMessage(),
            ], 500);
        }
    }

    public function updateLobData(Request $request)
    {
        $request->validate([
            'lob_name' => 'required|string|max:255',
            'lob_master_name' => 'required|string|max:255',
            'frontend_url' => 'required|string|max:255',
            'customer_frontend_url' => 'nullable|string|max:255',
            'lob_icon' => 'nullable|mimes:jpeg,png,jpg|max:2048',
            'is_enabled' => 'required|in:Y,N',
            'payment_url' => 'nullable|string|max:255',
        ]);
    
        $lob = lobMaster::find($request->id);
    
        if (!$lob) {
            return response()->json(['message' => 'LOB not found!'], 404);
        }
    
        $lob->lob_name = $request->lob_name;
        $lob->lob_master_name = $request->lob_master_name;
        $lob->frontend_url = $request->frontend_url;
        $lob->customer_frontend_url = $request->customer_frontend_url;
        $lob->payment_url = $request->payment_url;
        if ($request->hasFile('lob_icon')) {
            $logoFile = $request->file('lob_icon');
            $logoFileName = 'logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
            $logoPath = $logoFile->storeAs('broker_logo', $logoFileName, 'public');
            $lob->lob_icon = $logoPath;
        }
        $lob->is_enabled = $request->is_enabled;
    
        $lob->save();
    
        return response()->json([
            'status' => 200,
            'return_data' => $lob,
            'message' => 'LOB updated successfully!']);
    }

}
