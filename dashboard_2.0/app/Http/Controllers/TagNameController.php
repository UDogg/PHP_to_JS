<?php

namespace App\Http\Controllers;

use App\Models\Faq;
use App\Models\TagName;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;

class TagNameController extends Controller
{
    protected $authUser;
    public function __construct()
    {
        $this->authUser = Auth::user();
    }
    public function index(Request $request)
    {

        $faq = TagName::all();


        return view('tag_master', compact('faq'));

    }
    public function show(Request $request)
    {
        $listPermission = "Create FAQ.view";
        if (!$this->authUser->can($listPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $tags = TagName::select('tag_id', 'tag_name')->get();

        return response()->json([
            'status' => 200,
            'data' => $tags,
            'message' => 'Tags fetched successfully'
        ], 200);

    }

    public function store(Request $request)
    {
        $listPermission = "Create FAQ.edit";
        if (!$this->authUser->can($listPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $rules = [
            'tag_name' => ['required', 'string'],

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

            $faq = new TagName();
            $faq->tag_name = $request->tag_name; // Store total minutes in the database


            $faq->save();

            if ($faq->save()) {
                return response()->json([
                    'status' => 200,
                    'return_data' => $faq,
                    'message' => 'Tag Created Successfully',
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
    public function update(Request $request)
    {
        $listPermission = "Create FAQ.edit";
        if (!$this->authUser->can($listPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }
        $rules = [
            'tag_name' => ['required', 'string'],

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

        $faq = TagName::find($request->id);

        if (!$faq) {
            return response()->json(
                [
                    'status' => 500,
                    'return_data' => [],
                    'message' => 'Tag data not found',
                ],
                500
            );
        }


        $faq->tag_name = $request->tag_name;



        $faq->save();
        return response()->json(
            [
                'status' => 200,
                'return_data' => $faq,
                'message' => 'Tag data updated successfully',
            ],
            200
        );
    }
    public function destroy(Request $request)
    {
        $listPermission = "Create FAQ.delete";
        if (!$this->authUser->can($listPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }


        $inactiveResponse = checkUserActivity($request);
        if ($inactiveResponse) {
            return $inactiveResponse;
        }

        $faq = TagName::where('tag_id', $request->id)->first();

        if ($faq) {
            $faqData = Faq::where('tag',$request->id)->update(['deleted_at' => now()]);
            $faq->delete();
            return response()->json(['message' => 'Tag Data deleted successfully']);
        } else {
            return response()->json(['message' => 'Tag Data not found or already deleted']);
        }
    }

}
