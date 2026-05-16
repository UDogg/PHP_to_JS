<?php

namespace App\Services;

use App\Models\MongoModel;
use Illuminate\Support\Carbon;
use App\Models\StagemasterModel;
use App\Models\substagemaster;

class BusinessMetricsService
{
    public function premiumCount(
        Carbon $startDate,
        Carbon $endDate,
        $lob,
        array $sellerTypeAgg,
        array $subStagesArr
    ) {
        $andConditions = [];

        $andConditions[] = [
            'lastupdated_time' => [
                '$gte' => $startDate->format('Y-m-d') . ' 00:00:00',
                '$lte' => $endDate->format('Y-m-d') . ' 23:59:59',
            ]
        ];

        $andConditions[] = [
            'transaction_stage' => [
                '$in' => $subStagesArr
            ]
        ];

        if (!empty($lob) && strtoupper($lob) !== 'ALL') {
            $andConditions[] = ['section' => $lob];
        }

        if (!empty($sellerTypeAgg)) {
            $andConditions[] = ['$or' => $sellerTypeAgg];
        }

        $matchQuery = ['$and' => $andConditions];

        $mongo2Data = MongoModel::raw(function ($collection) use ($matchQuery) {
            return $collection->aggregate([
                ['$match' => $matchQuery],
                [
                    '$group' => [
                        '_id' => null,
                        'total_premium' => [
                            '$sum' => [
                                '$toDouble' => ['$ifNull' => ['$premium_amount', 0]]
                            ]
                        ],
                        'policy_count' => ['$sum' => 1]
                    ]
                ]
            ]);
        });
        //dd($matchQuery);

        $result = $mongo2Data->toArray();



        return [
            'total_premium' => $result[0]['total_premium'] ?? 0,
            'policy_count'  => $result[0]['policy_count'] ?? 0,
        ];
        
    }

    public function policyCountByStage(
    Carbon $startDate,
    Carbon $endDate,
    string $stageName,
    $lob,
    array $sellerTypeAgg
) {
    $stage = StagemasterModel::where('stage_name', $stageName)->first();

    if (!$stage) {
        return 0;
    }

    $subStageIds = array_filter(explode(',', $stage->sub_stage_name));

    $subStagesArr = substagemaster::whereIn('id', $subStageIds)
        ->pluck('sub_stage_name')
        ->toArray();

    $andConditions = [];

    $andConditions[] = [
        'lastupdated_time' => [
            '$gte' => $startDate->format('Y-m-d') . ' 00:00:00',
            '$lte' => $endDate->format('Y-m-d') . ' 23:59:59',
        ]
    ];

    $andConditions[] = [
        'transaction_stage' => ['$in' => $subStagesArr]
    ];

    if (!empty($lob) && strtoupper($lob) !== 'ALL') {
        $andConditions[] = ['section' => $lob];
    }

    if (!empty($sellerTypeAgg)) {
        $andConditions[] = ['$or' => $sellerTypeAgg];
    }

    $matchQuery = ['$and' => $andConditions];

    $data = MongoModel::raw(function ($collection) use ($matchQuery) {
        return $collection->aggregate([
            ['$match' => $matchQuery],
            [
                '$group' => [
                    '_id' => null,
                    'policy_count' => ['$sum' => 1]
                ]
            ]
        ]);
    });

    $result = $data->toArray();

    return (int) ($result[0]['policy_count'] ?? 0);
}

public function conversionPercentage(int $quoted, int $issued)
{
    if ($quoted === 0) {
        return $issued === 0 ? 0 : null;
    }

    return ($issued / $quoted) * 100;
}


}
