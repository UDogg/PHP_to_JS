<?php

namespace App\Services;

use App\Models\{
    PolicyStatusFilterMaster,
    StagemasterModel,
    substagemaster,
    MongoModel,
    lobMaster as lob_master,
    MisReportConfigurator,
    User
};
use Carbon\Carbon;
use Illuminate\Http\Request;
use Illuminate\Support\Arr;

class PolicyStatusCountService
{
    /**
     * Build MongoDB query with complex $and and $or operators
     * Uses same logic as PolicyStatusController::buildMongoQuery
     */
    private function buildMongoQuery(
        array $sections,
        string $startDate,
        string $endDate,
        array $transactionStages,
        array $usersIdWithTypetoFetch,
        User $user,
        bool|string $b2c_flag = false
    ): array {
        $rmCode = $user->employee_code ?? '';
        $canUseRmCode = !empty($rmCode) && $user->usertype == 1;
        
        $sellerOrConditions = [];
        
        if ($b2c_flag) {
            $sellerOrConditions[] = [
                'seller_type' => ['$in' => ['b2c', 'U']]
            ];
        }
        
        foreach ($usersIdWithTypetoFetch as $sellerType => $sellerIds) {
            // if (in_array($sellerType, ['b2c', 'U'])) {
            //     continue;
            // }
            
            $sellerIds = is_array($sellerIds) ? $sellerIds : [];
            
            if (empty($sellerIds)) {
                $sellerOrConditions[] = [
                    'seller_type' => $sellerType
                ];
                continue;
            }
            
            $typeConditions = [];
            
            $typeConditions[] = [
                'seller_id' => ['$in' => $sellerIds]
            ];
            
            if(config('fetch_sp_details')){
                if ($canUseRmCode && in_array($sellerType, ['E', 'SP'])) {
                    $typeConditions[] = [
                        'RmCode' => $rmCode
                    ];
                }
            }
            
            if (count($typeConditions) === 1) {
                $sellerOrConditions[] = [
                    '$and' => [
                        ['seller_type' => $sellerType],
                        $typeConditions[0]
                    ]
                ];
            } else {
                $sellerOrConditions[] = [
                    '$and' => [
                        ['seller_type' => $sellerType],
                        ['$or' => $typeConditions]
                    ]
                ];
            }
        }
        
        // Build the main query
        $query = [
            '$and' => [
                [
                    'section' => [
                        '$in' => $sections
                    ]
                ],
                [
                    'lastupdated_time' => [
                        '$gte' => $startDate,
                        '$lte' => $endDate
                    ]
                ]
            ]
        ];
        
        // Only add transaction_stage filter if stages are provided
        if (!empty($transactionStages)) {
            $query['$and'][] = [
                'transaction_stage' => [
                    '$in' => $transactionStages
                ]
            ];
        }
        
        // Add seller filtering conditions if any exist
        if (!empty($sellerOrConditions)) {
            $query['$and'][] = [
                '$or' => $sellerOrConditions
            ];
        }
        return $query;
    }

    /**
     * Get policy status counts with MongoDB aggregation
     * 
     * @param Request $request
     * @param User $user
     * @param array $filter_value
     * @param array $usersIdWithTypetoFetch
     * @param bool|string $b2c_flag
     * @param string|null $data_flag
     * @param array $section
     * @return array
     */
    public function getPolicyStatusCounts(
        Request $request,
        User $user,
        array $filter_value,
        array $usersIdWithTypetoFetch,
        bool|string $b2c_flag,
        ?string $data_flag,
        array $section = []
    ): array
    {
        // Determine date range (same logic as controller)
        // Note: We don't filter by transaction_stage for count service to get counts for all stages
        $isRenewal = $request->is_renewal == 'Y' ? true : false;
        $queryStartDate = '';
        $queryEndDate = '';
        if (!empty($request['startDate']) && !empty($request['endDate']) && !$isRenewal && empty($filter_value['Report Type'])) {
            try {
                $startDateObj = Carbon::createFromFormat('d/m/Y', trim($request['startDate']));
                $endDateObj = Carbon::createFromFormat('d/m/Y', trim($request['endDate']));
                $queryStartDate = $startDateObj->format('Y-m-d') . " 00:00:00";
                $queryEndDate = $endDateObj->format('Y-m-d') . " 23:59:59";
            } catch (\Exception $e) {
                // Invalid date format
            }
        } elseif (!empty($filter_value['Report Type']) && is_array($filter_value['Report Type'])) {
            try {
                $startDateObj = Carbon::createFromFormat('d/m/Y', trim($request['startDate']));
                $endDateObj = Carbon::createFromFormat('d/m/Y', trim($request['endDate']));
                $queryStartDate = $startDateObj->format('Y-m-d') . " 00:00:00";
                $queryEndDate = $endDateObj->format('Y-m-d') . " 23:59:59";
            } catch (\Exception $e) {
                // Invalid date format
            }
        }
        
        // Use buildMongoQuery if we have all required parameters
        // Note: For count service, we don't filter by transaction_stage to get counts for all stages
        $useMongoQuery = false;
        if (!empty($queryStartDate) && !empty($queryEndDate) && !empty($section)) {
            $mongoQuery = $this->buildMongoQuery(
                sections: $section,
                startDate: $queryStartDate,
                endDate: $queryEndDate,
                transactionStages: [], // Empty array - don't filter by transaction_stage for counts
                usersIdWithTypetoFetch: $usersIdWithTypetoFetch,
                user: $user,
                b2c_flag: $b2c_flag
            );
            
            $matchStage = $mongoQuery;
            $useMongoQuery = true;
            
            // Add UTM filter for usertype 4 if needed
            if ($user->usertype == 4) {
                $utmParams = activeRoleCodeMappingUser();
                $utmOr = [];
                
                foreach ($utmParams as $key => $value) {
                    if ($key == 'utm_medium') $key = 'utm_media';
                    $valueArr = explode(',', $value);
                    $utmOr[] = [
                        'broker_' . $key => count($valueArr) > 1 ? ['$in' => $valueArr] : $valueArr[0]
                    ];
                }
                
                if (!empty($utmOr)) {
                    // Add UTM filter to the existing $and conditions
                    $matchStage['$and'][] = ['$or' => $utmOr];
                }
            }
        } else {
            // Fallback to original logic if conditions not met
            $matchStage = [];

            // Section filter
            $matchStage['section'] = $request['lobFilter'] ?? ['$in' => $section];

            // Dynamic filters
            if (!empty($filter_value)) {
                foreach ($filter_value as $filterKey => $filterValue) {
                    if ($filterKey === 'Report Type') {
                        continue;
                    }
                    $result = PolicyStatusFilterMaster::join('policystatus_column_master as b', 'policy_status_filter_master.column', '=', 'b.id')
                        ->select('b.column_name', 'policy_status_filter_master.value')
                        ->where('policy_status_filter_master.filtername', $filterKey)
                        ->where('policy_status_filter_master.value', $filterValue)
                        ->first();

                    if ($result) {
                        $matchStage[$result->column_name] = ['$in' => explode(',', $result->value)];
                    }
                }
            }

            // Date filter
            if (!empty($request['startDate']) && !empty($request['endDate'])) {
                try {
                    $start = Carbon::createFromFormat('d/m/Y', $request['startDate'])->startOfDay()->toDateTimeString();
                    $end = Carbon::createFromFormat('d/m/Y', $request['endDate'])->endOfDay()->toDateTimeString();

                    $matchStage['lastupdated_time'] = ['$gte' => $start, '$lte' => $end];
                } catch (\Exception $e) {
                    // Invalid date format handling (optional)
                }
            }

            // UTM filter (for usertype 4)
            $orConditions = [];
            if ($user->usertype == 4 ) {

                $utmParams = activeRoleCodeMappingUser();
             
                $utmOr = [];   

                foreach ($utmParams as $key => $value) {
            
                    if ($key == 'utm_medium') $key = 'utm_media';
            
                    $valueArr = explode(',', $value);
            
                    $utmOr[] = [
                        'broker_' . $key => count($valueArr) > 1 ? ['$in' => $valueArr] : $valueArr[0]
                    ];
                }
            
                if (!empty($utmOr)) {
                    $orConditions[] = ['$or' => $utmOr];  
                }
            }

            // Seller filters (only if not using mongo query)
            $sellerFilters = [];

            if (!empty($b2c_flag)) {
                $sellerFilters[] = ['seller_type' => ['$in' => ['b2c', 'U']]];
            }

            if (!empty($data_flag)) {
                $sellerFilters[] = [
                    'seller_type' => ['$in' => explode(',', $data_flag)],
                    'RmCode' => $user->employee_code
                ];        
            } else {
            
                foreach ($usersIdWithTypetoFetch as $type => $ids) {
                    $orBlock = [];
            
                    if (!empty($ids)) {
                        $orBlock[] = ['seller_id' => ['$in' => $ids]];
                    }        
                    $orBlock[] = ['RmCode' => $user->employee_code];
            
                    $sellerFilters[] = [
                        '$and' => [
                            ['seller_type' => $type],
                            ['$or' => $orBlock]
                        ]
                    ];
                }
            }
            
            if (!empty($sellerFilters)) {
                $orConditions[] = ['$or' => $sellerFilters];
            }      

            if (!empty($orConditions)) {
                $matchStage['$and'] = $orConditions;
            }
        }

        // MongoDB aggregation pipeline
        $pipeline = [
            ['$match' => $matchStage],
            ['$group' => ['_id' => '$transaction_stage', 'count' => ['$sum' => 1]]],
            ['$project' => ['sub_stage_name' => '$_id', 'count' => 1, '_id' => 0]]
        ];

        if(config('fetch_sp_details')){
            $result = MongoModel::raw(fn($collection) => $collection->aggregate($pipeline));

            $subStageCounts = collect(iterator_to_array($result))
                ->mapWithKeys(fn($item) => [trim($item['sub_stage_name'] ?? '') => $item['count']])
                ->toArray();
    
            // Get all stages and substages
            $allStages = StagemasterModel::orderBy('priority')->get()->keyBy('stage_name');
            $allSubStages = substagemaster::all()->keyBy('id');
    
            // Map stages to sub-stage names
            $stageSubstageMap = $allStages->mapWithKeys(function ($stage) use ($allSubStages) {
                $subStageIds = array_filter(explode(',', $stage->sub_stage_name));
                $subStageNames = collect($subStageIds)
                    ->map(fn($id) => trim(optional($allSubStages[$id])->sub_stage_name))
                    ->filter()
                    ->toArray();
                return [$stage->stage_name => $subStageNames];
            });
    
            // Final count per stage
            return $stageSubstageMap->map(function ($subStages) use ($subStageCounts) {
                return collect($subStages)->sum(fn($s) => $subStageCounts[$s] ?? 0);
            })->toArray();
        }else{
            $finalCounts = [];

            $sellerIdRef = null;
   
           foreach ($pipeline[0]['$match']['$and'] as $andIdx => $andBlock) {
               if (!empty($andBlock['$or'])) {
                   foreach ($andBlock['$or'] as $orIdx => $orBlock) {
                       if (
                           isset($orBlock['$and'][1]['seller_id']['$in']) &&
                           count($orBlock['$and'][1]['seller_id']['$in']) > 500
                       ) {
                           $sellerIdRef = &$pipeline[0]['$match']['$and'][$andIdx]['$or'][$orIdx]['$and'][1]['seller_id']['$in'];
                           break 2;
                       }
                   }
               }
           }
   
           if ($sellerIdRef !== null) {
   
               $allSellerIds = $sellerIdRef;
               $chunks = array_chunk($allSellerIds, 500);
   
               foreach ($chunks as $chunk) {
   
                   $sellerIdRef = $chunk;
   
                   $cursor = MongoModel::raw(
                       fn($collection) => $collection->aggregate($pipeline, ['allowDiskUse' => true])
                   );
   
                   foreach ($cursor as $row) {
                       $stage = trim($row['sub_stage_name'] ?? '');
                       if ($stage === '') continue;
   
                       $finalCounts[$stage] = ($finalCounts[$stage] ?? 0) + (int) $row['count'];
                   }
               }
   
           } else {
   
               $cursor = MongoModel::raw(
                   fn($collection) => $collection->aggregate($pipeline, ['allowDiskUse' => true])
               );
   
               foreach ($cursor as $row) {
                   $stage = trim($row['sub_stage_name'] ?? '');
                   if ($stage === '') continue;
   
                   $finalCounts[$stage] = ($finalCounts[$stage] ?? 0) + (int) $row['count'];
               }
           }
   
           $subStageCounts = $finalCounts;
   
   
           $allStages = StagemasterModel::orderBy('priority')->get()->keyBy('stage_name');
           $allSubStages = substagemaster::all()->keyBy('id');
   
           $stageSubstageMap = $allStages->mapWithKeys(function ($stage) use ($allSubStages) {
               $subStageIds = array_filter(explode(',', $stage->sub_stage_name));
               $subStageNames = collect($subStageIds)
                   ->map(fn($id) => trim(optional($allSubStages[$id])->sub_stage_name))
                   ->filter()
                   ->toArray();
               return [$stage->stage_name => $subStageNames];
           });
   
           return $stageSubstageMap->map(function ($subStages) use ($subStageCounts) {
               return collect($subStages)->sum(fn($s) => $subStageCounts[$s] ?? 0);
           })->toArray();
        }

    }
}
