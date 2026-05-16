<?php

namespace App\Http\Controllers;

use App\Models\MenuMasterModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Storage;

class DocumentConfigController extends Controller
{
    public function documentConfigIndex()
    {
        $modules = MenuMasterModel::all();
        return view('documentConfig.index', compact('modules'));
    }  
    public function uploadDocument(Request $request)
    {
        $request->validate([
            'moduletag' => 'required',
            'uploadDoc' => 'required|mimes:pdf,doc,docx,xls,xlsx|max:2048', 
        ]);
        $moduletag = $request->moduletag;
        if (!Storage::exists('public/uploads/documents')) {
            Storage::makeDirectory('public/uploads/documents');
        }
        try {
            if ($request->hasFile('uploadDoc')) {
                $file = $request->file('uploadDoc');
                $fileName = time() . '_' . $file->getClientOriginalName();
                $file->storeAs('uploads/documents', $fileName, 'public');
    
                MenuMasterModel::where('id', $moduletag)->update([
                    'filename' => $fileName,
                ]);
    
                return back()->with('success', 'Document uploaded and saved successfully!');
            }
    
            return back()->with('error', 'No file uploaded.');
        } catch (\Exception $e) {
            return back()->with('error', 'An error occurred while uploading the document: ' . $e->getMessage());
        }

    }

    public function edit($id)
    {
        $document = MenuMasterModel::findOrFail($id);
        return view('documentConfig.edit', compact('document'));
    }


    public function update(Request $request, $id)
    {
        $request->validate([
            'uploadDoc' => 'nullable|mimes:pdf,doc,docx,xls,xlsx|max:2048',
        ]);

        $document = MenuMasterModel::findOrFail($id);

        if ($request->hasFile('uploadDoc')) {
            $file = $request->file('uploadDoc');
            $fileName = time() . '_' . $file->getClientOriginalName();
            $file->storeAs('uploads/documents', $fileName, 'public');
            $document->filename = $fileName;
        }

        $document->save();

        return redirect()->route('documentConfigIndex')->with('success', 'Document updated successfully!');
    }

    public function downloadDocument(Request $request, $id)
    {
        
        $document = MenuMasterModel::find($id);

        if (!$document) {
            $errorResponse = [
                'success' => false,
                'message' => 'Document not found.',
            ];
            return $request->expectsJson()
                ? response()->json($errorResponse, 404)
                : back()->with('error', $errorResponse['message']);
        }

        $filePath = 'uploads/documents/' . $document->filename;

        if (Storage::disk('public')->exists($filePath)) {
            $file = storage_path('app/public/' . $filePath);

            return response()->download($file, $document->filename);
        }

        $errorResponse = [
            'success' => false,
            'message' => 'Document file not found in storage.',
        ];

        return $request->expectsJson()
            ? response()->json($errorResponse, 404)
            : back()->with('error', $errorResponse['message']);
    }


}
