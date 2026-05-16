<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\MongoModel;
use App\Models\MisReportConfigurator;
use App\Models\StagemasterModel;
use App\Models\substagemaster;
use Illuminate\Support\Facades\Storage;

class PullApiRapperController extends Controller
{

    public function getdata(Request $request)
    {
        $request->validate([
            'start_date' => 'required',
            'end_date' => 'required',
            'seller_type' => 'array',
            'seller_username' => 'array'
        ]);
        $stage= StagemasterModel::select('id','sub_stage_name')->where('stage_name','Issued')->first();
        $subStageList = $stage->sub_stage_name;
        $subStageList = explode(',', $subStageList);
        $SubStages  = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $transactionStages = $SubStages->pluck('sub_stage_name')->toArray();
        $startDate = $request->input('start_date');
        $endDate = $request->input('end_date');

        $sellerType = $request->input('seller_type', ['b2c']);  // Default to ['b2c']
        $sellerUsername = $request->input('seller_username'); 
        $sellerType = empty($sellerType) ? ['b2c'] : $sellerType;
        $query = MongoModel::select('*')
        ->whereIn('seller_type', $sellerType)
        ->whereIn('transaction_stage', $transactionStages);
                    
        if ($request->has('seller_username') && !empty($sellerUsername)) {
            $query->whereIn('seller_username', $sellerUsername);
        }
        if ($startDate && $endDate) {
                $startDate = date('Y-m-d 00:00:00', strtotime($startDate));
                $endDate = date('Y-m-d 23:59:59', strtotime($endDate));
            $query->whereBetween('lastupdated_time', [$startDate, $endDate]);
        }
    
        $MisReportColumn = $query->get();
        $MisReportColumn->transform(function ($item) {
            if (!empty($item->policy_doc_path)) {
                $oldUrl = $item->policy_doc_path;
    
                 $parsedUrl = parse_url($oldUrl);
                 $fileKey = isset($parsedUrl['path']) ? ltrim($parsedUrl['path'], '/') : ''; 
                 if (!empty($fileKey)) {
                    $newUrl = \Illuminate\Support\Facades\Storage::disk('s3')->temporaryUrl(
                        $fileKey,
                        now()->addDays(7)
                    );
    
                    $item->policy_doc_path = $newUrl;
                }
            }
             return $item;
        });
        if ($MisReportColumn->isEmpty()) {
            return response()->json([
                'status' => 404,
                'message' => 'No Records Found'
            ]);
        } else {
            return response()->json([
                'status' => 200,
                'return_data' => $MisReportColumn,
                'message' => 'Records Found'
            ]);
        }
    }
}
