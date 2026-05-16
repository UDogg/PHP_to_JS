<?php

namespace App\Http\Controllers;


use App\Models\MongoModel;
use Illuminate\Support\Str;
use Carbon\Carbon;
use Illuminate\Container\Attributes\DB;
use Illuminate\Http\Request;

class AnalyticsController extends Controller
{
    public function analysis(Request $request)
    {
        $page = $request->input('page', 1);  
        $perPage = $request->input('per_page', 10);  

        $traceId = $request->input('trace_id');
        $proposerName = $request->input('proposer_name');
        $proposerMobile = $request->input('proposer_mobile');
        $sellerType = $request->input('seller_type');
        $sellerMobile = $request->input('seller_mobile');
        $sellerUsername = $request->input('seller_username');
        $sellerName = $request->input('seller_name');
        $businessType = $request->input('business_type');
        $companyAlias = $request->input('company_alias');
        $policyType = $request->input('policy_type');

        $pipeline = [];

        $traceId ? $pipeline[] = ['$match' => ['trace_id' => ['$in' => $traceId]]] : null;
        $proposerName ? $pipeline[] = ['$match' => ['proposer_name' => ['$in' => $proposerName]]] : null;
        $proposerMobile ? $pipeline[] = ['$match' => ['proposer_mobile' => ['$in' => $proposerMobile]]] : null;
        $sellerType ? $pipeline[] = ['$match' => ['seller_type' => ['$in' => $sellerType]]] : null;
        $sellerMobile ? $pipeline[] = ['$match' => ['seller_mobile' => ['$in' => $sellerMobile]]] : null;
        $sellerUsername ? $pipeline[] = ['$match' => ['seller_username' => ['$in' => $sellerUsername]]] : null;
        $sellerName ? $pipeline[] = ['$match' => ['seller_name' => ['$in' => $sellerName]]] : null;
        $businessType ? $pipeline[] = ['$match' => ['business_type' => ['$in' => $businessType]]] : null;
        $companyAlias ? $pipeline[] = ['$match' => ['company_alias' => ['$in' => $companyAlias]]] : null;
        $policyType ? $pipeline[] = ['$match' => ['policy_type' => ['$in' => $policyType]]] : null;


        $pipeline[] = [
            '$facet' => [
                'data' => [ // This is where you get the filtered data
                    ['$skip' => ($page - 1) * $perPage], // Pagination (skip)
                    ['$limit' => $perPage] // Pagination (limit)
                ],
                'totalCount' => [
                    ['$count' => 'total'] // Count the total number of documents
                ]
            ]
        ];
 
        // Run the aggregation query
        $results = MongoModel::raw(function ($collection) use ($pipeline) {
            return $collection->aggregate($pipeline);
        });

        return response()->json($results);

    }
}
