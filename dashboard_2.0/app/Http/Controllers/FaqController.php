<?php

namespace App\Http\Controllers;

use App\Models\Faq;
use App\Models\TagName;
use App\Exports\FaqExport;
use App\Imports\FaqImport;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;
use Illuminate\Http\JsonResponse;
use Illuminate\Support\Facades\Storage;

class FaqController extends Controller
{
    public function index(Request $request)
    {

        $faq = Faq::join('tag_names', 'faqs.tag', '=', 'tag_names.tag_id')
                ->select('faqs.*', 'tag_names.tag_name')
                ->get();


        $tag_name = TagName::all();

        return view('faq_master', compact('faq', 'tag_name'));
    }

    public function store(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $rules = [
            'tag' => ['required', 'string'],
            'question' => ['required', 'string'],
            'answer' => ['required', 'string'],
            'status' => ['required','in:Active,Inactive']
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Invalid request data',
                ],
                500
            );
        } else {

            $faq = new Faq();
            $faq->tag = $request->tag;
            $faq->question = $request->question;
            $faq->answer = $request->answer;
            $faq->status = $request->status;

            $faq->save();

            if ($faq->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $faq,
                    'message' => 'FAQ Created Successfully',
                ], 200);
            } else {
                return response()->json(
                    [
                        'status' => 500,
                        'return_data' => [],
                        'message' => 'Invalid request data',
                    ],
                    500
                );
            }
        }
    }
    public function destroy(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $faq = Faq::where('faq_id', $request->id)->first();

        if ($faq) {
            $faq->delete();
            return response()->json(['message' => 'FAQ Data deleted successfully']);
        } else {
            return response()->json(['message' => 'FAQ Data not found or already deleted']);
        }
    }
    public function update(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $rules = [
            'tag' => ['required', 'string'],
            'question' => ['required', 'string'],
            'answer' => ['required', 'string'],
            'status' => ['required','in:Active,Inactive']
        ];

        $validator = Validator::make($request->all(), $rules);

        if ($validator->fails()) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Validation failed',
                    'errors' => $validator->errors(),
                ],
                500
            );
        }

        $faq = Faq::find($request->id);

        if (!$faq) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Company not found',
                ],
                500
            );
        }


        $faq->tag = $request->tag;
        $faq->question = $request->question;
        $faq->answer = $request->answer;
        $faq->status = $request->status;


        $faq->save();
        return response()->json(
            [
                'status' => 200,
                'return_data' => $faq,
                'message' => 'FAQ data updated successfully',
            ],
            200
        );
    }

    public function listTag(Request $request)
    {
        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        if ($request->has('tag_id')) {
            $request->validate([
                'tag_id' => 'integer',
            ]);

            $tag = TagName::find($request->tag_id);
            if (!$tag) {
                return response()->json([
                    'error' => 'Tag not found'
                ], 500);
            }

            $faqs = Faq::where('tag', $request->tag_id)
                        ->select('question', 'answer', 'status')
                        ->get();

            return response()->json([
                'column_head'=> [
                    [
                        "header"=> "Sr",
                        "accessorKey"=> "sr",
                        "isActions"=> false,
                    ],
                    [
                        "header"=> "Heading",
                        "accessorKey"=> "heading",
                        "isActions"=> false,
                    ],
                    [
                        "header"=> "Actions",
                        "accessorKey"=> "actions",
                        "isActions"=> false,
                    ]
                ],
                'Tag name' => $tag->tag_name,
                'FAQ' => $faqs
            ], 200);
        }


        $faqs = Faq::with('tagName')
                    ->select('question', 'answer', 'status', 'tag')
                    ->get();


        $faqsWithTag = $faqs->map(function ($faq) {
            return [
                'Tag name' => $faq->tagName ? $faq->tagName->tag_name : 'Unknown Tag',
                'Question' => $faq->question,
                'Answer' => $faq->answer,
                'Status' => $faq->status
            ];
        });

        return response()->json([
            'FAQ' => $faqsWithTag
        ], 200);


    }
    public function exportFaqs()
    {

        $excelFileName = 'file_' . time() . '.xlsx';
            Excel::store(new FaqExport(), $excelFileName, 'public');
            $fileUrl = Storage::disk('public')->url($excelFileName);
            return [
                'status' => 'success',
                'message' => 'File is ready for download.',
                'download_link' => $fileUrl,
            ];
    }
    public function uploadFaqs(Request $request)
    {
        $authUser = Auth::user();
        $uploadPermission = "Create FAQ.upload";
        if (!$authUser->can($uploadPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }
       
        $request->validate([
            'file' => 'required|file|mimes:xlsx',
            'tag_id' => 'required|integer|exists:tag_names,tag_id',
        ]);

        $tagId = $request->input('tag_id');

        Excel::import(new FaqImport($tagId), $request->file('file'));

        return response()->json([
            'status' => 'success',
            'message' => 'FAQs uploaded successfully!',
        ]);
    }



}
