<?php

namespace App\Http\Controllers;

use App\Exports\CrossSellListDataExport;
use App\Exports\RenewalDataExport;
use App\Jobs\ExportLargeExcel;
use App\Models\Broker;
use App\Models\ExcelDownloadLog;
use App\Models\lobMaster;
use App\Models\Marquee;
use App\Models\masterCompany;
use App\Models\MongoModel;
use App\Models\StagemasterModel;
use App\Models\substagemaster;
use App\Models\User;
use App\Models\userTypes;
use DateTimeZone;
use Illuminate\Http\Request;
use Illuminate\Pagination\LengthAwarePaginator;
use Illuminate\Support\Carbon;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Str;
use Maatwebsite\Excel\Facades\Excel;
use MongoDB\BSON\UTCDateTime;
use Illuminate\Support\Facades\DB; 
use Illuminate\Support\Facades\Log; 

class DashboardApis extends Controller
{
    //
    protected $UserId;

    protected $usertypeIdentifier;

    protected $userHierarchyLists;

    public function __construct(Request $request)
    {
        if ($request->has('empIds') && ! empty($request->empIds)) {

            $user = User::select('usertype')->where('id', $request->empIds)->first();
            $this->UserId = $user;
            $this->UserId->id = $request->empIds;

        } else {
            $user = Auth::user();
            $this->UserId = $user;
            $this->usertypeIdentifier = userTypes::select('Identifier')->where('id', $this->UserId->usertype)->first()['Identifier'];
        }
    }

    public function getUserhierarchy(Request $request)
    {
        $user = Auth::user();
        $b2c_flag = $user->is_b2cflag;
        $data_flag = $user->data_flag;
        $UserIdentifier = getUserTypeFromToken();
        $usertypeId = $user->usertype;
        $userId = $user->id;
        $isAdmin = $user->is_admin;
        $dataFetchFrom = config('data_fetch_from_old') ? 'old_user_id' : 'id';

        // Override user if `user_id` is present in the request
        if (!empty($request['user_id'])) {
            $user = User::with('userType')
                ->where('id', $request['user_id'])
                ->first(); // fetches model directly

            if (!$user) {
                return response()->json([
                    'status' => 200,
                    'message' => 'User not found'
                ], 200);
            }

            $UserIdentifier = userTypes::where('id', $user->usertype)->first()->Identifier;
            $usertypeId = $user->usertype;
            $userId = $user->id;
            $isAdmin = $user->is_admin;
        }


        if ($usertypeId == 4) {
            $sellerTypeAgg[] = [
                'seller_type' => ['$in' => ['b2c', 'U']],
            ];
        } elseif ($isAdmin == 'Y') {

            switch ($usertypeId) {
                case '1':
                    $sellerTypeAgg[] = [
                        'seller_type' => ['$in' => ['E', 'P', 'Partner', 'SP']],
                    ];
                    break;
                case '2':
                    $sellerTypeAgg[] = [
                        'seller_type' => ['$in' => ['P']],
                    ];
                    break;
                case '3':
                    $sellerTypeAgg[] = [
                        'seller_type' => ['$in' => ['Partner']],
                    ];
                    break;
                case '7':
                    $sellerTypeAgg[] = [
                        'seller_type' => ['$in' => ['SP']],
                    ];
                        break;    
            }
        } else {
            if ($b2c_flag) {
                $sellerTypeAgg[] = [
                    '$and' => [
                        ['seller_type' => ['b2c', 'U']],
                    ],
                ];
            }
            if (! empty($data_flag)) {
                $sellerTypeAgg[] = [
                    '$and' => [
                        'seller_type' => ['$in' => explode(',', $data_flag)],
                    ],
                ];
            } else {

                $hierarchyData = getUserLowerHierarchy($userId, $usertypeId);
                if (empty($hierarchyData)) {
                    $usersIdWithTypetoFetch[$UserIdentifier] = [$user->{$dataFetchFrom}];

                } else {
                    $usersIdWithTypetoFetch = [
                        $UserIdentifier => array_column($hierarchyData, $dataFetchFrom),
                    ];
                    $allemployeedata = array_column($hierarchyData, 'employee_code');

                    $usersIdWithTypetoFetch[$UserIdentifier] = array_merge($usersIdWithTypetoFetch[$UserIdentifier], [$userId]);

                    if ($usertypeId == 1 || $usertypeId == 7) {
                        $usersIdWithTypetoFetch['SP'] = [$userId];
                        $finalMappingData = getMapPosPartner($allemployeedata);
                        $finalpospartnerdata = collect($finalMappingData)
                            ->groupBy('usertype')
                            ->mapWithKeys(function ($group, $key) use ($dataFetchFrom) {
                                return [
                                    $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck($dataFetchFrom)->all(),
                                ];
                            })
                            ->toArray();
                        if (! empty($finalpospartnerdata)) {
                            $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                        }
                    }

                }
                foreach ($usersIdWithTypetoFetch as $sellerType => $ids) {
                    $sellerTypeAgg[] = [
                        '$and' => [
                            ['seller_type' => $sellerType],
                            [
                                '$or' => [
                                    ['seller_id' => ['$in' => $ids]],
                                    ['RmCode' => $user->employee_code]
                                ]
                            ]
                        ]
                    ];                    
                }
            }
        }

        return $sellerTypeAgg;
    }

    private function transactionStagesQuery($stage = 'Issued')
    {
        $stage = StagemasterModel::select('id', 'sub_stage_name')->where('stage_name', $stage)->first();
        $subStageList = $stage->sub_stage_name;
        $subStageList = explode(',', $subStageList);
        $SubStages = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();

        return $subStagesArr;
        //        todo: use later for mongo query code optimization

    }

    private function PoliciesCount()
    {

        $stage = StagemasterModel::select('id', 'sub_stage_name')->where('stage_name', 'Issued')->first();
        $subStageList = $stage->sub_stage_name;
        $subStageList = explode(',', $subStageList);
        $SubStages = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();
        $lobQuery = $this->AllLobs();
        $sections = [];
        $userlist = $this->getUserhierarchy($request);

        foreach ($lobQuery as $key => $value) {
            $sections[] = $value['lob'];
        }
        $mongo2Data = MongoModel::raw(function ($collection) use ($subStagesArr, $sections, $userlist) {
            $sellerTypeAgg = [];
            if (! UserIsAdmin($this->UserId->id)) {
                $sellerTypeAgg[] = [
                    'seller_type' => $this->usertypeIdentifier,
                    'seller_id' => ['$in' => [1, 2, 3, 4]],
                ];
                if (! empty($userlist['PosUsers'])) {
                    $sellerTypeAgg[] = [
                        'seller_type' => 'P',
                        'seller_id' => ['$in' => [1, 2, 3, 4]],
                    ];
                }

            } else {
                $sellerTypeAgg[] = [
                    'seller_type' => ['$in' => [
                        $this->usertypeIdentifier, 'P', 'Partner', 'b2c',
                    ]],
                ];
            }

            return $collection->aggregate([
                [
                    '$match' => [
                        '$or' => $sellerTypeAgg,
                        'section' => ['$in' => $sections],
                        'transaction_stage' => [
                            '$in' => $subStagesArr,
                        ],

                    ],
                ],
                [
                    '$group' => [
                        '_id' => null,  // Group all the results
                        'count' => ['$sum' => 1],
                        'amount' => ['$sum' => '$premium_amount'],
                        'offline_count' => ['$sum' => [
                            '$cond' => [
                                ['$ifNull' => ['$is_offline_entry', false]],
                                1,
                                0,
                            ],
                        ],
                        ],
                        'online_count' => [
                            '$sum' => [
                                '$cond' => [
                                    [
                                        '$or' => [
                                            ['$eq' => ['$is_offline_entry', 1]],  // Count where is_offline_entry is 1
                                            ['$not' => ['$is_offline_entry']],     // Count where is_offline_entry does not exist
                                        ],
                                    ],
                                    1,
                                    0,
                                ],
                            ]],
                        'CARCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'CAR']], 1, 0],
                            ],
                        ],
                        'CarAmount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'CAR']], '$premium_amount', 0],
                            ],
                        ],
                        'PCVCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'PCV']], 1, 0],
                            ],
                        ],
                        'PCVamount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'PCV']], '$premium_amount', 0],
                            ],
                        ],
                        'GCVCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'GCV']], 1, 0],

                            ]],
                        'GCVamount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'GCV']], '$premium_amount', 0],
                            ],
                        ],
                        'HealthCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'health']], 1, 0],
                            ],
                        ],
                        'HealthAmount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'health']], '$premium_amount', 0],
                            ],
                        ],
                    ],
                ],
                [
                    '$project' => [
                        'count' => 1,
                        'amount' => 1,
                        'OfflineCount' => '$online_count',
                        'onlineCount' => '$offline_count',
                        'car' => [
                            'count' => '$CARCount',
                            'amount' => '$CarAmount',
                        ],
                        'pcv' => [
                            'count' => '$PCVCount',
                            'amount' => '$PCVamount',
                        ],
                        'gcv' => [
                            'count' => '$GCVCount',
                            'amount' => '$GCVamount',
                        ],
                        'health' => [
                            'count' => '$HealthCount',
                            'amount' => '$HealthAmount',
                        ],
                    ],
                ],
            ]);
        });

        return $mongo2Data;
    }

    public function DashboardData()
    {
        $policiesCount = $this->PoliciesCount();

        return response()->json([
            'status' => '200',
            'return_data' => $policiesCount,
        ]);
    }

    protected function AllLobs()
    {
        $lobQuery = lobMaster::select('id', 'lob_name', 'lob')->where('is_enabled', 'Y')->get()->toArray();

        return $lobQuery;

    }

    public function LobWiseStagePoliciesCount(Request $request)
    {
        $sections = $group = [];
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $lobQuery = $this->AllLobs();
        foreach ($lobQuery as $key => $value) {
            $sections[] = $value['lob'];
            $group[$value['lob']] = [
                '$push' => [
                    'Policies' => [
                        '$sum' => [
                            '$cond' => ['$eq' => ['$section', $value['lob']], 1, 0],
                        ],
                    ],
                    'Amount' => [
                        '$sum' => [
                            '$cond' => ['$eq' => ['$section', $value['lob']], '$premium_amount', 0],
                        ],
                    ],
                ],
            ];
        }

        $transactionStages = [
            'Policy Issued',
            'Policy Issued pdf generated',
            'Policy Issued, but pdf not generated',
            'Payment Success',
        ];

        $matchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => [
                    '$in' => $transactionStages,
                ],
            ],
        ];

        $groupStage = [
            '$group' => [
                '_id' => '$section',
                'totalPolicies' => [
                    '$sum' => 1,
                ],
                'totalAmount' => [
                    '$sum' => '$premium_amount',
                ],
            ],
        ];

        $projectStage = [
            '$project' => [
                'section' => '$_id',
                'totalPolicies' => 1,
                'totalAmount' => 1,
                '_id' => 0,
            ],
        ];

        $query = [$matchStage, $groupStage, $projectStage];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        return $results;
    }

    public function AllCompanies()
    {
        $CompanyQuery = masterCompany::select('company_id', 'company_name', 'company_shortname')->get()->toArray();

        return $CompanyQuery;
    }

    public function IcWisePremium(Request $request)
    {
        $lob = $request->input('lob');
        $company_alias = [];
        $CompanyQuery = $this->AllCompanies();

        $companyMap = collect($CompanyQuery)->pluck('company_name', 'company_shortname')->toArray();

        foreach ($CompanyQuery as $value) {
            $company_alias[] = $value['company_shortname'];
        }

        $sellerTypeAgg = $this->dataFlagCheck($request);
        $transactionStages = $this->transactionStagesQuery();

        $match = [
            '$or' => $sellerTypeAgg,
            'company_alias' => ['$in' => $company_alias],
            'transaction_stage' => ['$in' => $transactionStages],
        ];
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $match['section'] = $lob;
        }

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];

        if ($request->has('startDate') && $request->has('endDate')) {
            $startDate = new \DateTime($request->input('startDate'));
            $endDate = new \DateTime($request->input('endDate'));

            $matchStage['$match']['lastupdated_time'] = [
                '$gte' => $startDate->format('Y-m-d H:i:s'),
                '$lt' => $endDate->format('Y-m-d H:i:s'),
            ];
        }

        $groupStage = [
            '$group' => [
                '_id' => '$company_alias',
                'policies' => ['$sum' => 1],
                'premium' => ['$sum' => '$premium_amount'],
            ],
        ];

        $sortStage = [
            '$sort' => ['premium' => -1],
        ];

        $addRankStage = [
            '$group' => [
                '_id' => null,
                'results' => ['$push' => [
                    'insurance_company' => '$_id',
                    'policies' => '$policies',
                    'premium' => '$premium',
                ]],
            ],
        ];

        $unwindStage = [
            '$unwind' => '$results',
        ];

        $rankStage = [
            '$group' => [
                '_id' => null,
                'results' => ['$push' => '$results'],
                'totalCount' => ['$sum' => 1],
            ],
        ];

        $addRankFieldStage = [
            '$project' => [
                'results' => [
                    '$map' => [
                        'input' => ['$range' => [0, '$totalCount']],
                        'as' => 'index',
                        'in' => [
                            'rank' => ['$add' => ['$$index', 1]],
                            'insurance_company' => ['$arrayElemAt' => ['$results.insurance_company', '$$index']],
                            'policies' => ['$arrayElemAt' => ['$results.policies', '$$index']],
                            'premium' => ['$arrayElemAt' => ['$results.premium', '$$index']],
                            // [
                                // '$round' => [
                                //     ['$arrayElemAt' => ['$results.premium', '$$index']],
                                //     2,
                                // ],
                            // ],
                        ],
                    ],
                ],
            ],
        ];

        $finalProjectStage = [
            '$project' => [
                'results' => 1,
                '_id' => 0,
            ],
        ];

        $query = [
            $matchStage,
            $groupStage,
            $sortStage,
            $addRankStage,
            $unwindStage,
            $rankStage,
            $addRankFieldStage,
            $finalProjectStage,
        ];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        $returnData = [];
        foreach ($results as $result) {
            foreach ($result['results'] as $item) {
                $item['insurance_company'] = $companyMap[$item['insurance_company']] ?? $item['insurance_company'];
                $returnData[] = $item;
            }
        }

        if (empty($returnData)) {
            $returnData[] = [
                'rank' => 0,
                'insurance_company' => null,
                'premium' => 0,
                'policies' => 0,
            ];
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Rank',
                    'accessorKey' => 'rank',
                    'isActions' => false,
                ],
                [
                    'header' => 'Insurance_Company',
                    'accessorKey' => 'insurance_company',
                    'isActions' => false,
                ],
                [
                    'header' => 'Premium',
                    'accessorKey' => 'premium',
                    'isActions' => false,
                ],
                [
                    'header' => 'Policies',
                    'accessorKey' => 'policies',
                    'isActions' => false,
                ],
            ],
            'return_data' => $returnData,
            'message' => 'Records Found',
        ]);
    }

    public function monthWisePremium(Request $request)
    {
        $lob = $request->input('lob');
        // $sellerTypeAgg = $this->getUserhierarchy($request);
        $sellerTypeAgg = $this->dataFlagCheck($request);
        $monthNames = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];

        $transactionStages = $this->transactionStagesQuery();

        $year = $request->has('year') ? (int) $request->year : (int) date('Y');
        if ($year === (int) date('Y')) {
            $currentMonth = now()->month;
            $endDate = Carbon::now()->endOfDay();
        } else {
            $currentMonth = 12;
        }

        $match = [
            'transaction_stage' => ['$in' => $transactionStages],
            '$or' => $sellerTypeAgg,
            '$expr' => [
                '$eq' => [
                    ['$year' => ['$dateFromString' => ['dateString' => '$lastupdated_time']]],
                    $year,
                ],
            ],
        ];
        if ($year === (int) date('Y')) {
            $match['lastupdated_time'] = ['$lte' => $endDate->format('Y-m-d H:i:s')];
        }
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $match['section'] = $lob;
        }

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];

        $projectStage = [
            '$project' => [
                'month' => ['$month' => ['$dateFromString' => ['dateString' => '$lastupdated_time']]],
                'premium_amount' => '$premium_amount',
                'is_offline_entry' => '$is_offline_entry',
                'offline_policy_premium_count' => ['$ifNull' => ['$offline_policy_premium_count', 0]],
                'online_policy_premium_count' => ['$ifNull' => ['$online_policy_premium_count', 0]],
            ],
        ];

        $groupStage = [
            '$group' => [
                '_id' => '$month',
                'total_premium' => ['$sum' => '$premium_amount'],
                'policies' => ['$sum' => 1],
                'offline_policy_premium_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_offline_entry', '1']], '$premium_amount', 0],
                    ],
                ],

                // Online policy count and premium
                'online_policy_premium_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_offline_entry', '0']], '$premium_amount', 0],
                    ],
                ],
            ],
        ];

        $sortStage = [
            '$sort' => ['_id' => 1],
        ];

        $finalProjectStage = [
            '$project' => [
                'month' => '$_id',
                'total_premium' => 1,
                'offline_policy_premium_count' => 1,
                'online_policy_premium_count' => 1,
                '_id' => 0,
            ],
        ];

        $query = [$matchStage, $projectStage, $groupStage, $sortStage, $finalProjectStage];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        // Initialize only months from January till current month
        $finalResults = [];
        for ($i = 1; $i <= $currentMonth; $i++) {
            $finalResults[$monthNames[$i - 1]] = [
                'month' => $monthNames[$i - 1],
                'total_premium' => 0,
                'offline_policy_premium_count' => 0,
                'online_policy_premium_count' => 0,
            ];
        }

        // Populate the months that have data
        foreach ($results as $result) {
            if (isset($result['month']) && $result['month'] <= $currentMonth) { // only till current month
                $monthName = $monthNames[$result['month'] - 1];
                $finalResults[$monthName]['total_premium'] = $result['total_premium'];
                $finalResults[$monthName]['offline_policy_premium_count'] = $result['offline_policy_premium_count'];
                $finalResults[$monthName]['online_policy_premium_count'] = $result['online_policy_premium_count'];
            }
        }

        $finalResults = array_values($finalResults);

        return response()->json([
            'status' => 200,
            'return_data' => $finalResults,
            'message' => 'Records Found',
        ]);
    }

    public function userWisePremium(Request $request)
    {
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $sellerEmail = MongoModel::raw(function ($collection) {
            return $collection->distinct('seller_email', []);
        });

        $transactionStages = $this->transactionStagesQuery();

        $match = [
            '$or' => $sellerTypeAgg,
            'seller_email' => ['$in' => $sellerEmail],
            'transaction_stage' => ['$in' => $transactionStages],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];

        if ($request->has('startDate') && $request->has('endDate')) {
            $startDate = (new \DateTime($request->input('startDate')))->format('Y-m-d H:i:s');
            $endDate = (new \DateTime($request->input('endDate')))->format('Y-m-d H:i:s');

            $matchStage['$match']['lastupdated_time'] = [
                '$gte' => $startDate,
                '$lt' => $endDate,
            ];
        }
        $groupStage = [
            '$group' => [
                '_id' => '$seller_email',
                'policies' => ['$sum' => 1],
                'premium' => ['$sum' => '$premium_amount'],
            ],
        ];

        $sortStage = [
            '$sort' => ['premium' => -1],
        ];
        $results = MongoModel::raw(function ($collection) use ($matchStage, $groupStage, $sortStage) {
            return $collection->aggregate([$matchStage, $groupStage, $sortStage]);
        });

        if ($results->isEmpty()) {
            return response()->json(['status' => 204, 'message' => 'No records found']);
        }

        $resultsArray = $results->toArray();
        $rankedResults = array_map(function ($result, $index) {
            return [
                'rank' => $index + 1,
                'user_email' => $result['_id'],
                'premium' => $result['premium'],
                'policies' => $result['policies'],
            ];
        }, $resultsArray, array_keys($resultsArray));

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Rank',
                    'accessorKey' => 'rank',
                    'isActions' => false,
                ],
                [
                    'header' => 'User_Email',
                    'accessorKey' => 'user_email',
                    'isActions' => false,
                ],
                [
                    'header' => 'Premium',
                    'accessorKey' => 'premium',
                    'isActions' => false,
                ],
                [
                    'header' => 'Policies',
                    'accessorKey' => 'policies',
                    'isActions' => false,
                ],
            ],
            'return_data' => $rankedResults,
            'message' => 'Records Found',
        ]);
    }

    public function customerWisePremium(Request $request)
    {
        $sellerTypeAgg = $this->getUserhierarchy($request);
        // $proposerNames = MongoModel::raw(function ($collection) {
        //     return $collection->distinct('proposer_name', []);
        // });

        $transactionStages = $this->transactionStagesQuery();
        $match = [
            '$or' => $sellerTypeAgg,
            // 'proposer_name' => ['$in' => $proposerNames],
            'transaction_stage' => ['$in' => $transactionStages],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];

        $groupStage = [
            '$group' => [
                '_id' => '$proposer_name',
                'policies' => ['$sum' => 1],
                'premium' => ['$sum' => ['$toInt' => ['$round' => ['$premium_amount', 0]]]],
                'proposer_mobile' => ['$first' => '$proposer_mobile'],
            ],
        ];

        $sortStage = [
            '$sort' => ['premium' => -1],
        ];

        $limitStage = [
            '$limit' => 10,
        ];

        $results = MongoModel::raw(function ($collection) use ($matchStage, $groupStage, $sortStage, $limitStage) {
            return $collection->aggregate([
                $matchStage,
                $groupStage,
                $sortStage,
                $limitStage,
            ]);
        });

        $resultsArray = $results->toArray();
        if (empty($resultsArray)) {
            $rankedResults = [[
                'rank' => 0,
                'user_name' => null,
                'premium' => 0,
                'policies' => 0,
                'proposer_mobile' => null,
            ]];
        } else {
            $rankedResults = array_map(function ($result, $index) {
                return [
                    'rank' => $index + 1,
                    'user_name' => $result['_id'] ?? $result['id'] ?? null,
                    'premium' => $result['premium'] ?? 0,
                    'policies' => $result['policies'] ?? 0,
                    'proposer_mobile' => $result['proposer_mobile'] ?? null,
                ];
            }, $resultsArray, array_keys($resultsArray));
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Rank',
                    'accessorKey' => 'rank',
                    'isActions' => false,
                ],
                [
                    'header' => 'User_Name',
                    'accessorKey' => 'user_name',
                    'isActions' => false,
                ],
                [
                    'header' => 'Premium',
                    'accessorKey' => 'premium',
                    'isActions' => false,
                ],
                [
                    'header' => 'Policies',
                    'accessorKey' => 'policies',
                    'isActions' => false,
                ],
                [
                    'header' => 'Proposer_Mobile',
                    'accessorKey' => 'proposer_mobile',
                    'isActions' => false,
                ],
            ],
            'return_data' => $rankedResults,
            'message' => empty($resultsArray) ? 'No records found' : 'Records Found',
        ]);
    }

    public function upcomingAndExpiredRenewals(Request $request)
    {
        $sections = [];
        $sellerTypeAgg = $this->getUserhierarchy($request);

        $lob = $request->input('lob');
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $sections = [$lob];
        } else {
            $lobQuery = $this->AllLobs();

            foreach ($lobQuery as $value) {
                $sections[] = $value['lob'];
            }
        }

        $transactionStages = $this->transactionStagesQuery();

        // Dates for upcoming renewals
        $startDateUpcoming = new UTCDateTime(now()->startOfDay()->getTimestamp() * 1000);
        $endDateUpcoming = new UTCDateTime(now()->addMonth()->startOfDay()->getTimestamp() * 1000);

        // Dates for expired renewals
        $startDateExpired = new UTCDateTime(now()->subDays(30)->startOfDay()->getTimestamp() * 1000);
        $endDateExpired = new UTCDateTime(now()->subDay()->startOfDay()->getTimestamp() * 1000);

        // Format dates
        $startDateUpcomingFormatted = $startDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateUpcomingFormatted = $endDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $startDateExpiredFormatted = $startDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateExpiredFormatted = $endDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');

        // Query for upcoming renewals

        $match = [
            '$or' => $sellerTypeAgg,
            'section' => ['$in' => $sections],
            'transaction_stage' => ['$in' => $transactionStages],
            'policy_end_date' => [
                '$gte' => $startDateUpcomingFormatted,
                '$lt' => $endDateUpcomingFormatted,
            ],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $upcomingMatchStage = [
            '$match' => $match,
        ];

        $upcomingGroupStage = [
            '$group' => [
                '_id' => '$section',
                'count' => ['$sum' => 1],
            ],
        ];

        $upcomingSortStage = [
            '$sort' => ['count' => -1],
        ];

        $upcomingFinalProjectStage = [
            '$project' => [
                'id' => ['$add' => [1, ['$indexOfArray' => ['$section', '$_id']]]],
                'lob' => '$_id',
                'count' => 1,
                '_id' => 0,
            ],
        ];

        // Query for expired renewals
        $expiredMatchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $startDateExpiredFormatted,
                    '$lt' => $endDateExpiredFormatted,
                ],
            ],
        ];

        $expiredGroupStage = [
            '$group' => [
                '_id' => '$section',
                'count' => ['$sum' => 1],
            ],
        ];

        $expiredSortStage = [
            '$sort' => ['count' => -1],
        ];

        $expiredFinalProjectStage = [
            '$project' => [
                'id' => ['$add' => [1, ['$indexOfArray' => ['$section', '$_id']]]],
                'lob' => '$_id',
                'count' => 1,
                '_id' => 0,
            ],
        ];

        $upcomingQuery = [
            $upcomingMatchStage,
            $upcomingGroupStage,
            $upcomingSortStage,
            $upcomingFinalProjectStage,
        ];

        $expiredQuery = [
            $expiredMatchStage,
            $expiredGroupStage,
            $expiredSortStage,
            $expiredFinalProjectStage,
        ];

        $upcomingResults = MongoModel::raw(fn ($collection) => $collection->aggregate($upcomingQuery))->toArray();
        $expiredResults = MongoModel::raw(fn ($collection) => $collection->aggregate($expiredQuery))->toArray();

        // Adjusting the IDs based on highest count
        $upcomingResultsWithId = [];
        if (! empty($upcomingResults)) {
            foreach ($upcomingResults as $index => $result) {
                $result['id'] = $index + 1;
                $upcomingResultsWithId[] = $result;
            }
        }

        $expiredResultsWithId = [];
        if (! empty($expiredResults)) {
            foreach ($expiredResults as $index => $result) {
                $result['id'] = $index + 1;
                $expiredResultsWithId[] = $result;
            }
        }

        return response()->json([
            'status' => 200,
            'return_data' => [
                'upcoming' => $upcomingResultsWithId,
                'expired' => $expiredResultsWithId,
            ],
            'message' => 'Records Found',
        ]);
    }

    public function retrieveTraceIdData(Request $request)
    {
        $user = Auth::user();
        $traceId = $request->input('trace_id');

        if (empty($traceId)) {
            return response()->json([
                'success' => false,
                'message' => 'Please enter a trace ID.',
            ], 400);
        }

        $results = MongoModel::where('trace_id', $traceId)->first();

        if (! $results) {
            return response()->json([
                'status' => 500,
                'message' => 'Invalid trace ID.',
            ], 404);
        }

        $data = $results->toArray();

        $roleIds = $user->roles->pluck('id')->toArray(); 

        $moduleId = DB::table('mask_configuration_master')
            ->where('status', 'Y')
            ->where('usertype', $user->usertype)
            ->whereIn('role', $roleIds)
            ->value('id');
        $maskConfigs = DB::table('role_pi_data_mapping')
            ->where('module_id', $moduleId)
            ->where('is_enabled', 'Y')
            ->get()
            ->keyBy('field_name');

        foreach ($data as $key => $value) {

            if (isset($maskConfigs[$key])) {

                $config = $maskConfigs[$key];

                if ($config->mask_type == 'Full Masking') {
                    $data[$key] = fullMaskValue($value);
                }

                elseif ($config->mask_type == 'Partial Masking') {
                    $data[$key] = partialMaskValue($value, $config->mask_formula);
                }
            }
        }

        return response()->json([
            'status' => 200,
            'return_data' => $data,
        ]);
    }

    public function lobWisePolicyData(Request $request)
    {
        $lob = $request->input('lob');
        $sections = $group = [];
        // $sellerTypeAgg = $this->getUserhierarchy($request);
        $sellerTypeAgg = $this->dataFlagCheck($request);

        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $sections = [$lob];
        } else {
            $lobQuery = $this->AllLobs();
            foreach ($lobQuery as $key => $value) {
                $sections[] = $value['lob'];
            }
        }
        if ($request->has('seller_type') && is_array($request->seller_type)) {

            $sellerTypeAgg = array_map(function ($type) {
                return ['seller_type' => $type];
            }, $request->seller_type);
        
        }

        $transactionStages = $this->transactionStagesQuery();

        $andConditions = [
        ['section' => ['$in' => $sections]],
        ['transaction_stage' => ['$in' => $transactionStages]],
        ['$or' => $sellerTypeAgg],  
        ];
        

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                $utmOrConditions = [];

                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }
                    $brokerKey = 'broker_' . $key;
                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $utmOrConditions[] = [
                            $brokerKey => ['$in' => $valueArr]
                        ];
                    } else {
                        $utmOrConditions[] = [
                            $brokerKey => $value
                        ];
                    }
                }
                 $andConditions[] = ['$or' => $utmOrConditions];
            }
        }

        $matchStage = [
        '$match' => [
            '$and' => $andConditions
        ]
       ];


    if ($request->has('startDate') && $request->has('endDate') && $request->has('date_type') && $request->input('date_type') == 'transaction_date') {

        $startDate = $request->input('startDate').' 00:00:00';
        $endDate = $request->input('endDate').' 23:59:59';

        $matchStage['$match']['transaction_date'] = [
            '$gte' => $startDate,
            '$lte' => $endDate,
        ];
    }elseif ($request->has('startDate') && $request->has('endDate') && !$request->has('date_type')) {

        $startDate = $request->input('startDate').' 00:00:00';
        $endDate = $request->input('endDate').' 23:59:59';

        $matchStage['$match']['lastupdated_time'] = [
            '$gte' => $startDate,
            '$lte' => $endDate,
        ];
    }

        // Seller ID filtering (handle empty empIds)
        if ($request->has('empIds')) {
            $empIds = $request->input('empIds');
            if (! empty($empIds)) {
                if (! is_array($empIds)) {
                    $empIds = [$empIds];
                }
                $matchStage['$match']['seller_id'] = ['$in' => $empIds];
            }
        }

        $groupStage = [
            '$group' => [
                '_id' => '$section',
                'totalPolicies' => ['$sum' => 1],
                'totalAmount' => ['$sum' => '$premium_amount'],
                'offline_policy_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_offline_entry', '1']], 1, 0],
                    ],
                ],
                'offline_policy_premium_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_offline_entry', '1']], '$premium_amount', 0],
                    ],
                ],

                // Online policy count and premium
                'online_policy_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_offline_entry', '0']], 1, 0],
                    ],
                ],
                'online_policy_premium_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_offline_entry', '0']], '$premium_amount', 0],
                    ],
                ],
            ],
	];

    if ($request->has('groupData') && $request->input('groupData') == 'datewise' && $request->input('date_type') == 'transaction_date') {
	    $groupStage['$group']['_id'] = [
                'section' => '$section',
	    	'date' => [
                    '$dateToString' => [
                        'format' => '%Y-%m-%d',
		    	'date' => [
                             '$toDate' => '$transaction_date'
                    	]		
		    ]
                ]
	    ];
	}else if ($request->has('groupData') && $request->input('groupData') == 'datewise'  && $request->input('date_type') != 'transaction_date') {
	    $groupStage['$group']['_id'] = [
                'section' => '$section',
	    	'date' => [
                    '$dateToString' => [
                        'format' => '%Y-%m-%d',
		    	'date' => [
                             '$toDate' => '$lastupdated_time'
                    	]		
		    ]
                ]
	    ];
	}

        // Project stage
        $projectStage = [
            '$project' => [
                'lob' => '$_id',
                'Issued' => '$totalPolicies',
                'premium' => '$totalAmount',
                // [
                //     '$round' => ['$totalAmount', 0],
                // ],
                'offline_policy_count' => ['$ifNull' => ['$offline_policy_count', 0]],
                'offline_policy_premium_count' => ['$ifNull' => ['$offline_policy_premium_count', 0]],
                'online_policy_count' => ['$ifNull' => ['$online_policy_count', 0]],
                'online_policy_premium_count' => ['$ifNull' => ['$online_policy_premium_count', 0]],
                '_id' => 0,
            ],
	];

	if ($request->has('groupData') && $request->input('groupData') == 'datewise') {
	    $projectStage['$project']['lob'] = '$_id.section';
            $projectStage['$project']['date'] = '$_id.date';
	}

	$sortStage = [
            '$sort' => [
                'lob' => 1,   // section ASC
                'date' => 1   // date ASC (use -1 for DESC)
            ]
        ];

        // Build query
        $query = [$matchStage, $groupStage, $projectStage, $sortStage];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        if (empty($results)) {
            return response()->json([
                'status' => 500,
                'return_data' => [
                    'lob' => null,
                    'Issued' => 0,
                    'premium' => 0,
                ],
                'message' => 'No records found',
            ]);
        }

        return response()->json([
            'status' => 200,
            'return_data' => $results,
            'message' => 'Records Found',
        ]);
    }

    public function conversionRate(Request $request)
    {
        $monthNames = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
        $transactionStages = $this->transactionStagesQuery();
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $year = $request->has('year') ? (int) $request->year : (int) date('Y');
        if ($year === (int) date('Y')) {
            $currentMonth = now()->month;
        } else {
            $currentMonth = 12;
        }

        $match = [
            'transaction_stage' => ['$in' => $transactionStages],
            '$or' => $sellerTypeAgg,
            '$expr' => [
                '$eq' => [
                    ['$year' => ['$dateFromString' => ['dateString' => '$lastupdated_time']]],
                    $year,
                ],
            ],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];

        $projectStage = [
            '$project' => [
                'month' => ['$month' => ['$dateFromString' => ['dateString' => '$lastupdated_time']]],
                'section' => '$section',
                'proposer_mobile' => '$proposer_mobile',
                'policy_issued_count' => [
                    '$cond' => [
                        ['$eq' => ['$transaction_stage', 'Policy Issued']],
                        1,
                        0,
                    ],
                ],
            ],
        ];

        $groupStage = [
            '$group' => [
                '_id' => [
                    'month' => '$month',
                    'section' => '$section',
                ],
                'unique_proposer_mobiles' => ['$addToSet' => '$proposer_mobile'],
                'policy_issued_count' => ['$sum' => '$policy_issued_count'],
            ],
        ];

        $finalGroupStage = [
            '$group' => [
                '_id' => '$_id.month',
                'LOB' => [
                    '$push' => [
                        'section' => '$_id.section',
                        'unique_proposer_count' => ['$ifNull' => [['$size' => '$unique_proposer_mobiles'], 0]],
                        'policy_issued_count' => ['$ifNull' => ['$policy_issued_count', 0]],
                    ],
                ],
                'sum_of_unique_number' => ['$sum' => ['$ifNull' => [['$size' => '$unique_proposer_mobiles'], 0]]],
                'sum_of_policy_issued' => ['$sum' => ['$ifNull' => ['$policy_issued_count', 0]]],
            ],
        ];

        $rateProjectStage = [
            '$project' => [
                'month' => '$_id',
                'LOB' => [
                    '$map' => [
                        'input' => '$LOB',
                        'as' => 'lob',
                        'in' => [
                            'section' => '$$lob.section',
                            'unique_proposer_count' => '$$lob.unique_proposer_count',
                            'policy_issued_count' => '$$lob.policy_issued_count',
                            'value' => [
                                '$cond' => [
                                    ['$gt' => ['$$lob.policy_issued_count', 0]],
                                    ['$multiply' => [
                                        ['$divide' => ['$$lob.unique_proposer_count', '$$lob.policy_issued_count']],
                                        100,
                                    ]],
                                    0,
                                ],
                            ],
                        ],
                    ],
                ],
                'sum_of_unique_number' => ['$ifNull' => ['$sum_of_unique_number', 0]],
                'sum_of_policy_issued' => ['$ifNull' => ['$sum_of_policy_issued', 0]],
                'rate' => [
                    '$cond' => [
                        ['$gt' => ['$sum_of_policy_issued', 0]],
                        ['$multiply' => [
                            ['$divide' => ['$sum_of_unique_number', '$sum_of_policy_issued']],
                            100,
                        ]],
                        0,
                    ],
                ],
            ],
        ];

        $sortStage = [
            '$sort' => ['month' => 1],
        ];

        $query = [$matchStage, $projectStage, $groupStage, $finalGroupStage, $rateProjectStage, $sortStage];
        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        })->toArray();

        $formattedResults = [];
        foreach (range(1, $currentMonth) as $monthIndex) {
            $monthName = $monthNames[$monthIndex - 1];
            $existingData = collect($results)->firstWhere('month', $monthIndex);

            if ($existingData) {
                $existingData['month'] = $monthName;
                $formattedResults[] = $existingData;
            } else {
                $formattedResults[] = [
                    'month' => $monthName,
                    'LOB' => [[
                        'section' => null,
                        'unique_proposer_count' => 0,
                        'policy_issued_count' => 0,
                        'value' => 0,
                    ]],
                    'sum_of_unique_number' => 0,
                    'sum_of_policy_issued' => 0,
                    'rate' => 0,
                ];
            }
        }

        return response()->json([
            'status' => 200,
            'return_data' => $formattedResults,
            'message' => 'Records Found',
        ]);
    }

    public function lobWiseUniqueMobile(Request $request)
    {
        $transactionStages = $this->transactionStagesQuery();
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $lobQuery = $this->AllLobs();

        $sectionToLobId = [];
        if (is_array($lobQuery)) {
            $sectionToLobId = array_column($lobQuery, 'id', 'lob');
        }

        $match = [
            'transaction_stage' => ['$in' => $transactionStages],
            '$or' => $sellerTypeAgg,
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];

        $projectStage = [
            '$project' => [
                'section' => '$section',
                'proposer_mobile' => '$proposer_mobile',
            ],
        ];

        $groupStage = [
            '$group' => [
                '_id' => [
                    'section' => '$section',
                ],
                'unique_proposer_mobiles' => ['$addToSet' => '$proposer_mobile'],
            ],
        ];

        $query = [$matchStage, $projectStage, $groupStage];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        $sectionData = [];
        foreach ($results as $result) {
            $sectionData[$result['_id']['section']] = iterator_to_array($result['unique_proposer_mobiles']);
        }

        $allUniqueMobiles = [];
        foreach ($sectionData as $mobiles) {
            $allUniqueMobiles = array_merge($allUniqueMobiles, $mobiles);
        }
        $allUniqueMobiles = array_unique($allUniqueMobiles);
        $response = [];

        $missingDataRequest = $request->input('missing_data_request');
        $requestedSection = $request->input('section');
        $lobid = isset($sectionToLobId[$requestedSection]) ? $sectionToLobId[$requestedSection] : null;

        if ($requestedSection && isset($sectionData[$requestedSection])) {
            $mobilesInSection = $sectionData[$requestedSection];
            $missingMobiles = array_diff($allUniqueMobiles, $mobilesInSection);

            if ($missingDataRequest == 'count') {
                $response[] = [
                    'section' => $requestedSection,
                    'lob_id' => $lobid,
                    'missing_count' => count($missingMobiles),
                ];
            } else {
                $missingMobilesData = MongoModel::select('*')
                    ->whereIn('proposer_mobile', $missingMobiles)
                    ->whereIn('transaction_stage', $transactionStages)
                    ->get();

                $response[] = [
                    'section' => $requestedSection,
                    'lob_id' => $lobid,
                    'missing_data' => $missingMobilesData,
                ];
            }

            return response()->json([
                'status' => 200,
                'return_data' => $response,
                'message' => 'Records Found',
            ]);
        }

        foreach ($sectionData as $section => $mobiles) {
            $missingMobiles = array_diff($allUniqueMobiles, $mobiles);

            if ($missingDataRequest == 'data') {
                $missingMobilesData = MongoModel::select('*')
                    ->whereIn('proposer_mobile', $missingMobiles)
                    ->whereIn('transaction_stage', $transactionStages)
                    ->get();

                $response[] = [
                    'section' => $section,
                    'lob_id' => $sectionToLobId[$section] ?? null,
                    'missing_data' => $missingMobilesData,
                ];
            } else {
                $response[] = [
                    'section' => $section,
                    'lob_id' => $sectionToLobId[$section] ?? null,
                    'missing_count' => count($missingMobiles),
                ];
            }
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Proposer_Mobile',
                    'accessorKey' => 'proposer_mobile',
                    'type' => 'string',
                ],
                [
                    'header' => 'Seller_Name',
                    'accessorKey' => 'seller_name',
                    'type' => 'string',
                ],
                [
                    'header' => 'Vehicle_Registration_Number',
                    'accessorKey' => 'vehicle_registration_number',
                    'type' => 'string',
                ],
                [
                    'header' => 'Lob',
                    'accessorKey' => 'lob',
                    'type' => 'array',
                ],
                [
                    'header' => 'Sum_Assured',
                    'accessorKey' => 'sum_assured',
                    'type' => 'integer',
                ],
                [
                    'header' => 'Proposer_Name',
                    'accessorKey' => 'proposer_name',
                    'type' => 'string',
                ],
                [
                    'header' => 'Company_Name',
                    'accessorKey' => 'company_name',
                    'type' => 'string',
                ],
                [
                    'header' => 'Policy_No',
                    'accessorKey' => 'policy_no',
                    'type' => 'array',
                ],
                [
                    'header' => 'Trace_Id',
                    'accessorKey' => 'trace_id',
                    'type' => 'string',
                ],
            ],
            'return_data' => $response,
            'message' => 'Records Found',
        ]);
    }

    public function topLeaderBoard(Request $request)
    {
        $lob = $request->input('lob');
        $company_alias = array_column($this->AllCompanies(), 'company_shortname');
        $sellerTypeAgg = $this->dataFlagCheck($request);

        $transactionStages = $this->transactionStagesQuery();

        $match = [
            '$or' => $sellerTypeAgg,
            'company_alias' => ['$in' => $company_alias],
            'transaction_stage' => ['$in' => $transactionStages],
            'business_type' => ['$exists' => true],
            'policy_type' => ['$ne' => null],
        ];
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $match['section'] = $lob;
        } else {
            $match['section'] = ['$ne' => null];
        }

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStage = [
            '$match' => $match,
        ];
        if ($request->has('startDate') && $request->has('endDate')) {
            $startDate = new \DateTime($request->input('startDate'));
            $endDate = new \DateTime($request->input('endDate'));

            $matchStage['$match']['lastupdated_time'] = [
                '$gte' => $startDate->format('Y-m-d H:i:s'),
                '$lt' => $endDate->format('Y-m-d H:i:s'),
            ];
        }
        $groupStage = [
            '$group' => [
                '_id' => [
                    'company_alias' => '$company_alias',
                    'business_type' => '$business_type',
                    'section' => '$section',
                    'policy_type' => '$policy_type',
                ],
                'policies' => ['$sum' => 1],
                'premium' => ['$sum' => '$premium_amount'],
            ],
        ];

        $companyGroupStage = [
            '$group' => [
                '_id' => '$_id.company_alias',
                'business_types' => [
                    '$push' => [
                        'type' => '$_id.business_type',
                        'policy_count' => ['$sum' => '$policies'],
                    ],
                ],
                'policy_types' => [
                    '$push' => [
                        'type' => '$_id.policy_type',
                        'policy_count' => ['$sum' => '$policies'],
                    ],
                ],
                'total_policies' => ['$sum' => '$policies'],
                'total_premium' => ['$sum' => '$premium'],
                'lobs' => [
                    '$push' => [
                        'type' => '$_id.section',
                        'policy_count' => ['$sum' => '$policies'],
                    ],
                ],
            ],
        ];

        $sortStage = [
            '$sort' => ['total_policies' => -1],
        ];

        $finalProjectStage = [
            '$project' => [
                'insurance_company' => '$_id',
                'data' => [
                    'business_types' => '$business_types',
                    'policy_types' => '$policy_types',
                    'total_policies' => '$total_policies',
                    'total_premium' => '$total_premium',
                    'lobs' => '$lobs',
                ],
                '_id' => 0,
            ],
        ];

        $query = [
            $matchStage,
            $groupStage,
            $companyGroupStage,
            $sortStage,
            $finalProjectStage,
        ];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        $formattedResults = [];
        foreach ($results as $result) {
            $insuranceCompany = $result['insurance_company'];
            $data = $result['data'];

            $businessTypes = $policyTypes = $lobs = [];

            $categoryMap = [
                'business_types' => &$businessTypes,
                'policy_types' => &$policyTypes,
                'lobs' => &$lobs,
            ];

            foreach ($categoryMap as $category => &$targetArray) {
                foreach ($data[$category] as $item) {
                    if (isset($targetArray[$item['type']])) {
                        $targetArray[$item['type']] += $item['policy_count'];
                    } else {
                        $targetArray[$item['type']] = $item['policy_count'];
                    }
                }
            }

            $formattedResults[] = [
                'insurance_company' => $insuranceCompany,
                'total_policies' => $data['total_policies'],
                'total_premium' => round($data['total_premium'], 2),
                'lobs' => $lobs,
                'business_types' => $businessTypes,
                'policy_types' => $policyTypes,
            ];
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Insurance_Company',
                    'accessorKey' => 'insurance_company',
                    'type' => 'string',
                ],
                [
                    'header' => 'Business_Types',
                    'accessorKey' => 'business_types',
                    'type' => 'object',
                ],
                [
                    'header' => 'Policy_Types',
                    'accessorKey' => 'policy_types',
                    'type' => 'object',
                ],
                [
                    'header' => 'Total_Policies',
                    'accessorKey' => 'total_policies',
                    'type' => 'integer',
                ],
                [
                    'header' => 'Total_Premium',
                    'accessorKey' => 'total_premium',
                    'type' => 'integer',
                ],
                [
                    'header' => 'Lobs',
                    'accessorKey' => 'lobs',
                    'type' => 'object',
                ],
            ],
            'return_data' => $formattedResults,
            'message' => 'Records Found',
        ]);
    }

    public function topUsers(Request $request)
    {
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $company_alias = array_column($this->AllCompanies(), 'company_shortname');
        $sellerNames = MongoModel::raw(function ($collection) {
            return $collection->distinct('seller_name', []);
        });

        $transactionStages = $this->transactionStagesQuery();

        $match = [
            '$or' => $sellerTypeAgg,
            'seller_name' => ['$in' => $sellerNames],
            'transaction_stage' => ['$in' => $transactionStages],
            'company_alias' => ['$in' => $company_alias],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $matchStages = [
            '$match' => $match,
        ];

        $groupStage = [
            '$group' => [
                '_id' => [
                    'seller_name' => '$seller_name',
                    'company_alias' => '$company_alias',
                    'business_type' => '$business_type',
                    'section' => '$section',
                    'policy_type' => '$policy_type',
                ],
                'policies' => ['$sum' => 1],
                'premium' => ['$sum' => '$premium_amount'],
            ],
        ];

        $userGroupStage = [
            '$group' => [
                '_id' => '$_id.seller_name',
                'total_policies' => ['$sum' => '$policies'],
                'total_premium' => ['$sum' => '$premium'],
                'insurance_company' => [
                    '$push' => [
                        'type' => '$_id.company_alias',
                        'policy_count' => '$policies',
                    ],
                ],
                'business_types' => [
                    '$push' => [
                        'type' => '$_id.business_type',
                        'policy_count' => '$policies',
                    ],
                ],
                'policy_types' => [
                    '$push' => [
                        'type' => '$_id.policy_type',
                        'policy_count' => '$policies',
                    ],
                ],
                'lobs' => [
                    '$push' => [
                        'type' => '$_id.section',
                        'policy_count' => '$policies',
                    ],
                ],
            ],
        ];

        $sortStage = [
            '$sort' => ['total_policies' => -1],
        ];

        $results = MongoModel::raw(function ($collection) use ($matchStages, $groupStage, $userGroupStage, $sortStage) {
            return $collection->aggregate([$matchStages, $groupStage, $userGroupStage, $sortStage]);
        });
        if ($results->isEmpty()) {
            return response()->json([
                'status' => 204,
                'message' => 'No Records Found',
            ]);
        }

        $formattedResults = [];
        foreach ($results as $result) {

            $companies = $businessTypes = $policyTypes = $lobs = [];

            $seller = $result['_id'];
            $data = $result;
            $categoryMap = [
                'insurance_company' => &$companies,
                'business_types' => &$businessTypes,
                'policy_types' => &$policyTypes,
                'lobs' => &$lobs,
            ];

            foreach ($categoryMap as $field => &$array) {
                foreach ($data[$field] as $item) {
                    if (isset($item['type'], $item['policy_count'])) {
                        $array[$item['type']] = ($array[$item['type']] ?? 0) + $item['policy_count'];
                    }
                }
            }

            $formattedResults[] = [
                'user_name' => $seller,
                'insurance_company' => $companies,
                'total_policies' => $data['total_policies'],
                'total_premium' => round($data['total_premium'], 2),
                'lobs' => $lobs,
                'business_types' => $businessTypes,
                'policy_types' => $policyTypes,
            ];
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'User_Name',
                    'accessorKey' => 'user_name',
                    'type' => 'string',
                ],
                [
                    'header' => 'Insurance_Company',
                    'accessorKey' => 'insurance_company',
                    'type' => 'object',
                ],
                [
                    'header' => 'Total_Policies',
                    'accessorKey' => 'total_policies',
                    'type' => 'integer',
                ],
                [
                    'header' => 'Total_Premium',
                    'accessorKey' => 'total_premium',
                    'type' => 'integer',
                ],
                [
                    'header' => 'Business_Types',
                    'accessorKey' => 'business_types',
                    'type' => 'object',
                ],
                [
                    'header' => 'Policy_Types',
                    'accessorKey' => 'policy_types',
                    'type' => 'object',
                ],
                [
                    'header' => 'Lobs',
                    'accessorKey' => 'lobs',
                    'type' => 'object',
                ],
            ],
            'return_data' => $formattedResults,
            'message' => 'Records Found',
        ]);
    }

    public function lifetimePremiumDetails(Request $request)
    {
        $transactionStages = $this->transactionStagesQuery();
        // $sellerTypeAgg = $this->getUserhierarchy($request);
        $sellerTypeAgg = $this->dataFlagCheck($request);
        $lob = $request->input('lob');
        $user = Auth::user();

        if ($request->has('Option')) {
            $option = $request->input('Option');

            if ($option == 'Last_3_Month') {

                $startDate = Carbon::now()->subMonths(3)->addDay()->startOfDay();
                $endDate = Carbon::now()->endOfDay();

                $match = [
                    'transaction_stage' => ['$in' => $transactionStages],
                    '$or' => $sellerTypeAgg,
                    'lastupdated_time' => [
                        '$gte' => $startDate->format('Y-m-d H:i:s'),
                        '$lt' => $endDate->format('Y-m-d H:i:s'),
                    ],
                ];

            } elseif ($option == 'Year') {

                $selectedYear = $request->input('selectedYear')[0];
                $year = $selectedYear ?: now()->year;

                $startDate = Carbon::create($year, 1, 1)->startOfDay();
                $endDate = Carbon::create($year, 12, 31)->endOfDay();

                $match = [
                    'transaction_stage' => ['$in' => $transactionStages],
                    '$or' => $sellerTypeAgg,
                    'lastupdated_time' => [
                        '$gte' => $startDate->format('Y-m-d H:i:s'),
                        '$lt' => $endDate->format('Y-m-d H:i:s'),
                    ],
                ];

            } elseif ($option == 'Lifetime') {

                // No date filter, return all
                $match = [
                    'transaction_stage' => ['$in' => $transactionStages],
                    '$or' => $sellerTypeAgg,
                ];

            } elseif ($option == 'Financial_Year') {

                $selectedQuarters = $request->input('selectedQuarters', ['Q1', 'Q2', 'Q3', 'Q4']);
                $year = $request->input('Year', Carbon::now()->year);

                $currentMonth = Carbon::now()->month; // returns integer like 5

                $fyStartYear = ($currentMonth <= 4) ? $year - 1 : $year;
                $fyEndYear   = ($currentMonth <= 4) ? $year : $year + 1;

                $quarterRanges = [
                    'Q1' => [Carbon::create($fyStartYear, 4, 1), Carbon::create($fyStartYear, 6, 30, 23, 59, 59)], // Apr–Jun
                    'Q2' => [Carbon::create($fyStartYear, 7, 1), Carbon::create($fyStartYear, 9, 30, 23, 59, 59)], // Jul–Sep
                    'Q3' => [Carbon::create($fyStartYear, 10, 1), Carbon::create($fyStartYear, 12, 31, 23, 59, 59)], // Oct–Dec
                    'Q4' => [Carbon::create($fyEndYear, 1, 1), Carbon::create($fyEndYear, 3, 31, 23, 59, 59)], // Jan–Mar
                ];

                $quarterConditions = [];
                foreach ($selectedQuarters as $q) {
                    if (isset($quarterRanges[$q])) {
                        [$qStart, $qEnd] = $quarterRanges[$q];
                        $quarterConditions[] = [
                            'lastupdated_time' => [
                                '$gte' => $qStart->format('Y-m-d H:i:s'),
                                '$lt' => $qEnd->format('Y-m-d H:i:s'),
                            ],
                        ];
                    }
                }

                // Default to full FY if no quarters given
                if (empty($quarterConditions)) {
                    $quarterConditions[] = [
                        'lastupdated_time' => [
                            '$gte' => Carbon::create($fyStartYear, 4, 1)->format('Y-m-d H:i:s'),
                            '$lt' => Carbon::create($fyEndYear, 3, 31, 23, 59, 59)->format('Y-m-d H:i:s'),
                        ],
                    ];
                }

                $match = [
                    'transaction_stage' => ['$in' => $transactionStages],
                    '$and' => [
                        ['$or' => $sellerTypeAgg],
                        ['$or' => $quarterConditions],
                    ]
                ];                

            } else {
                // If unknown option, continue to period condition below
                goto PERIOD_LOGIC;
            }

        } elseif ($request->has('period')) {

            PERIOD_LOGIC:

            $period = $request->input('period');
            $startDate = null;
            $endDate = Carbon::now()->endOfDay();
            switch ($period) {
                case 'Q':
                    $startDate = Carbon::now()->subMonths(3)->startOfDay();
                    break;

                case 'H':
                    $startDate = Carbon::now()->subMonths(6)->startOfDay();
                    break;

                case 'Y':
                    $startDate = Carbon::now()->subMonths(12)->startOfDay();
                    break;
            }

            if ($startDate && $endDate) {
                $match = [
                    'transaction_stage' => ['$in' => $transactionStages],
                    '$or' => $sellerTypeAgg,
                    'lastupdated_time' => [
                        '$gte' => $startDate->format('Y-m-d H:i:s'),
                        '$lt' => $endDate->format('Y-m-d H:i:s'),
                    ],
                ];
            } else {
                $match = [
                    'transaction_stage' => ['$in' => $transactionStages],

                    '$or' => $sellerTypeAgg,
                ];
            }
        } else {
            $match = [
                'transaction_stage' => ['$in' => $transactionStages],

                '$or' => $sellerTypeAgg,
            ];
        }
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $match['section'] = $lob;
        }

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $pipeline = [
            [
                '$match' => $match,
            ],
            [
                '$group' => [
                    '_id' => null,
                    'total_policy_issued_count' => ['$sum' => 1],
                    'total_premium_amount' => ['$sum' => '$premium_amount'],

                    // Offline policy count and premium
                    'offline_policy_count' => [
                        '$sum' => [
                            '$cond' => [['$eq' => ['$is_offline_entry', '1']], 1, 0],
                        ],
                    ],
                    'offline_policy_premium_count' => [
                        '$sum' => [
                            '$cond' => [['$eq' => ['$is_offline_entry', '1']], '$premium_amount', 0],
                        ],
                    ],

                    // Online policy count and premium
                    'online_policy_count' => [
                        '$sum' => [
                            '$cond' => [['$eq' => ['$is_offline_entry', '0']], 1, 0],
                        ],
                    ],
                    'online_policy_premium_count' => [
                        '$sum' => [
                            '$cond' => [['$eq' => ['$is_offline_entry', '0']], '$premium_amount', 0],
                        ],
                    ],
                ],
            ],
            [
                '$project' => [
                    '_id' => 0,
                    'total_policy_issued_count' => ['$ifNull' => ['$total_policy_issued_count', 0]],
                    'total_premium_amount' => ['$ifNull' => ['$total_premium_amount', 0]],
                    'offline_policy_count' => ['$ifNull' => ['$offline_policy_count', 0]],
                    'offline_policy_premium_count' => ['$ifNull' => ['$offline_policy_premium_count', 0]],
                    'online_policy_count' => ['$ifNull' => ['$online_policy_count', 0]],
                    'online_policy_premium_count' => ['$ifNull' => ['$online_policy_premium_count', 0]],
                ],
            ],
        ];

        $results = MongoModel::raw(function ($collection) use ($pipeline) {
            return $collection->aggregate($pipeline);

        })->toArray();

        if (empty($results)) {
            $results = [
                [
                    'total_policy_issued_count' => 0,
                    'total_premium_amount' => 0,
                    'offline_policy_count' => 0,
                    'offline_policy_premium_count' => 0,
                    'online_policy_count' => 0,
                    'online_policy_premium_count' => 0,
                ],
            ];
        }

        return response()->json([
            'status' => 200,
            'return_data' => $results,
            'message' => 'Records Found',
        ]);
    }

    public function renewalConversionCount(Request $request)
    {
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $company_alias = array_column($this->AllCompanies(), 'company_shortname');
        $lobQuery = $this->AllLobs();
        $transactionStages = $this->transactionStagesQuery();

        $matchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'company_alias' => ['$in' => $company_alias],
                'transaction_stage' => ['$in' => $transactionStages],
            ],
        ];

        $groupStage = [
            '$group' => [
                '_id' => 0,
                'renewal_count' => [
                    '$sum' => [
                        '$cond' => [
                            [
                                '$or' => [
                                    ['$eq' => ['$is_renewal', 'Y']],
                                    ['$eq' => ['$is_renewed', 'Y']],
                                ],
                            ],
                            1,
                            0,
                        ],
                    ],
                ],
                'rollover_renewal_count' => [
                    '$sum' => [
                        '$cond' => [
                            ['$eq' => ['$rollover_renewal', 'Y']], 1, 0,
                        ],
                    ],
                ],
                'Portability' => [
                    '$sum' => [
                        '$cond' => [
                            ['$eq' => ['$is_ported', 'Y']], 1, 0,
                        ],
                    ],
                ],
                'Fresh' => [
                    '$sum' => [
                        '$cond' => [
                            ['$or' => [
                                ['$eq' => ['$is_renewal', 'N']],
                                ['$eq' => ['$is_renewed', 'N']],
                                ['$eq' => ['$rollover_renewal', 'N']],
                                ['$eq' => ['$is_ported', 'N']],
                            ]], 1, 0,
                        ],
                    ],
                ],
            ],
        ];

        $projectStage = [
            '$project' => [
                '_id' => 0,
                'Renewal' => '$renewal_count',
                'Rollover_renewal' => '$rollover_renewal_count',
                'Portability' => '$Portability',
                'Fresh' => '$Fresh',
            ],
        ];

        $query = [$matchStage, $groupStage, $projectStage];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        $returnData = ! empty($results) ? $results->toArray()[0] : [];

        return response()->json([
            'status' => 200,
            'return_data' => $returnData,
            'message' => 'Records Found',
        ]);
    }

    public function customerDetails(Request $request)
    {
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $transactionStages = $this->transactionStagesQuery();

        if ($request->has('proposer_name') || $request->has('proposer_mobile')) {
            $matchConditions = [];
            if ($request->has('proposer_name')) {
                $data = json_decode($request->getContent(), true);
                $proposerName = $data['proposer_name'] ?? null;
                $matchConditions[] = ['proposer_name' => $proposerName];

            }
            if ($request->has('proposer_mobile')) {
                $matchConditions[] = ['proposer_mobile' => $request->input('proposer_mobile')];
            }

            $match = [
                '$and' => [
                    ['$or' => $matchConditions],
                    ['$or' => $sellerTypeAgg],
                    ['transaction_stage' => ['$in' => $transactionStages]],
                ],
            ];

            if (Auth::user()->usertype == 4) {

                $utmParameter = activeRoleCodeMappingUser();

                if (! empty($utmParameter)) {
                    foreach ($utmParameter as $key => $value) {
                        if ($key == 'utm_medium') {
                            $key = 'utm_media';
                        }

                        $valueArr = explode(',', $value);

                        if (count($valueArr) > 1) {
                            $match['broker_'.$key] = ['$in' => $valueArr];
                        } else {
                            $match['broker_'.$key] = $value;
                        }
                    }
                }
            }

            $matchStage = [
                '$match' => $match,
            ];
        } else {
            return response()->json([
                'status' => 204,
                'message' => 'No records found',
                'return_data' => [],
            ]);
        }

        $groupStage = [
            '$group' => [
                '_id' => '$proposer_name',
                'premium' => ['$sum' => '$premium_amount'],
                'policies' => [
                    '$push' => [
                        'premium_amount' => '$premium_amount',
                        'policy_start_date' => '$policy_start_date',
                        'policy_end_date' => '$policy_end_date',
                        'lob' => '$section',
                        'trace_id' => '$trace_id',
                    ],
                ],
                'proposer_mobile' => ['$first' => '$proposer_mobile'],
            ],
        ];

        $sortStage = [
            '$sort' => ['premium' => -1],
        ];
        $results = MongoModel::raw(function ($collection) use ($matchStage, $groupStage, $sortStage) {
            return $collection->aggregate([$matchStage, $groupStage, $sortStage]);
        });

        if ($results->isEmpty()) {
            return response()->json(['status' => 204, 'message' => 'No records found']);
        }

        $resultsArray = json_decode(json_encode($results->toArray()), true);

        $rankedResults = [];
        foreach ($resultsArray as $index => $result) {
            $policies = [];

            foreach ($result['policies'] as $policy) {
                $policies[] = [
                    'premium_amount' => $policy['premium_amount'] ?? 0,
                    'policy_start_date' => $policy['policy_start_date'] ?? '',
                    'policy_end_date' => $policy['policy_end_date'] ?? '',
                    'lob' => $policy['lob'] ?? '',
                    'trace_id' => $policy['trace_id'] ?? '',
                ];
            }

            $rankedResults[] = [
                'rank' => $index + 1,
                'user_name' => $result['id'] ?? $result['_id'] ?? '',
                'premium' => $result['premium'],
                'proposer_mobile' => $result['proposer_mobile'],
                'policies' => $policies,
            ];
        }

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Premium_Amount',
                    'accessorKey' => 'premium_amount',
                    'type' => 'integer',
                ],
                [
                    'header' => 'Lob',
                    'accessorKey' => 'lob',
                    'type' => 'string',
                ],
                [
                    'header' => 'Policy_Start_Date',
                    'accessorKey' => 'policy_start_date',
                    'type' => 'string',
                ],
                [
                    'header' => 'Policy_End_Date',
                    'accessorKey' => 'policy_end_date',
                    'type' => 'string',
                ],
                [
                    'header' => 'Proposer_Mobile',
                    'accessorKey' => 'proposer_mobile',
                    'type' => 'string',
                ],
                [
                    'header' => 'Trace_Id',
                    'accessorKey' => 'trace_id',
                    'type' => 'string',
                ],
            ],
            'return_data' => $rankedResults,

            'message' => 'Records Found',
        ]);
    }

    public function renewalConversionLobswiseCount(Request $request)
    {
        $company_alias = array_column($this->AllCompanies(), 'company_shortname');
        $lobs = $this->AllLobs();
        $sectionQuery = $request->input('lob', []);
        $transactionStages = $this->transactionStagesQuery();
        $sellerTypeAgg = $this->getUserhierarchy($request);

        if (empty($sectionQuery)) {
            return response()->json([
                'status' => 'error',
                'message' => 'No LOB data provided in the request',
            ], 400);
        }

        $sections = is_array($sectionQuery)
            ? array_map(fn ($lob) => $lob['lob'], $sectionQuery)
            : [$sectionQuery];

        $matchStage = [
            '$match' => [
                'company_alias' => ['$in' => $company_alias],
                'transaction_stage' => ['$in' => $transactionStages],
                'section' => ['$in' => $sections],
                '$or' => $sellerTypeAgg,
            ],
        ];

        foreach (['is_renewal', 'rollover_renewal', 'is_ported'] as $field) {
            if ($request->has($field)) {
                $matchStage['$match'][$field] = $request->get($field);
            }
        }

        $groupStage = [
            '$group' => [
                '_id' => '$section',
                'section_count' => ['$sum' => 1],
                'renewal_count' => [
                    '$sum' => [
                        '$cond' => [
                            ['$or' => [
                                ['$eq' => ['$is_renewal', 'Y']],
                                ['$eq' => ['$is_renewed', 'Y']],
                            ]],
                            1,
                            0,
                        ],
                    ],
                ],
                'rollover_renewal_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$rollover_renewal', 'Y']], 1, 0],
                    ],
                ],
                'is_ported_count' => [
                    '$sum' => [
                        '$cond' => [['$eq' => ['$is_ported', 'Y']], 1, 0],
                    ],
                ],
                'Fresh' => [
                    '$sum' => [
                        '$cond' => [
                            ['$or' => [
                                ['$eq' => ['$is_renewal', 'N']],
                                ['$eq' => ['$is_renewed', 'N']],
                                ['$eq' => ['$rollover_renewal', 'N']],
                                ['$eq' => ['$is_ported', 'N']],
                            ]], 1, 0,
                        ],
                    ],
                ],
            ],
        ];

        $projectStage = [
            '$project' => [
                '_id' => 0,
                'LOB' => '$_id', // Rename `_id` to `LOB`
                'Total Policies' => '$section_count',
                'Renewal Count' => '$renewal_count',
                'Rollover Renewal Count' => '$rollover_renewal_count',
                'Portability Count' => '$is_ported_count',
                'Fresh' => '$Fresh',
            ],
        ];

        $query = [$matchStage, $groupStage, $projectStage];
        $results = MongoModel::raw(fn ($collection) => $collection->aggregate($query));

        return response()->json([
            'status' => 200,
            'return_data' => iterator_to_array($results),
            'message' => 'Records Found',
        ]);
    }

    public function renewalConversionData(Request $request)
    {
        if ($request->isMethod('get')) {
            return $this->renewalConversionCount($request);
        } elseif ($request->isMethod('post')) {
            return $this->renewalConversionLobswiseCount($request);
        }

        return response()->json([
            'status' => 200,
            'message' => 'Invalid request method',
        ], 405);
    }

    public function upcomingAndExpiredRenewalsDetails(Request $request)
    {
        $auth = Auth::user();
        $viewPermission = 'Renewal.view';
        $uploadPermission = 'Renewal.upload';

        if (! $auth->can($viewPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $columnHead = [
            [
                'header' => 'Renewal_Date',
                'accessorKey' => 'policy_end_date',
                'type' => 'string',
            ],
            [
                'header' => 'Customer_Mobile',
                'accessorKey' => 'proposer_mobile',
                'type' => 'string',
            ],
            [
                'header' => 'Customer_Name',
                'accessorKey' => 'proposer_name',
                'type' => 'integer',
            ],
            [
                'header' => 'CIF_Id',
                'accessorKey' => 'cif_id',
                'type' => 'string',
            ],
            [
                'header' => 'Vehicle_Registration_Number',
                'accessorKey' => 'vehicle_registration_number',
                'type' => 'string',
            ],
            [
                'header' => 'Lob',
                'accessorKey' => 'lob',
                'type' => 'array',
            ],
            [
                'header' => 'Company_Name',
                'accessorKey' => 'company_name',
                'type' => 'string',
            ],
            [
                'header' => 'Policy_No',
                'accessorKey' => 'policy_no',
                'type' => 'array',
            ],
            [
                'header' => 'Employee_Name',
                'accessorKey' => 'seller_name',
                'type' => 'integer',
            ],
            [
                'header' => 'Trace_Id',
                'accessorKey' => 'trace_id',
                'type' => 'string',
            ],
            [
                'header' => 'Sum_Assured',
                'accessorKey' => 'sum_assured',
                'type' => 'integer',
            ],
            [
                'header' => 'Business_Type',
                'accessorKey' => 'business_type',
                'type' => 'integer',
            ],
            [
                'header' => 'Status',
                'accessorKey' => 'status',
                'type' => 'integer',
            ],
        ];

        $sections = [];
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $lobQuery = $this->AllLobs();

        foreach ($lobQuery as $value) {
            $sections[] = $value['lob'];
        }

        $transactionStages = $this->transactionStagesQuery();

        // Dates for upcoming renewals
        $startDateUpcoming = new UTCDateTime(now()->startOfDay()->getTimestamp() * 1000);
        $endDateUpcoming = new UTCDateTime(now()->addMonth()->startOfDay()->getTimestamp() * 1000);

        // Dates for expired renewals
        $startDateExpired = new UTCDateTime(now()->subDays(30)->startOfDay()->getTimestamp() * 1000);
        $endDateExpired = new UTCDateTime(now()->subDay()->startOfDay()->getTimestamp() * 1000);

        // Format dates
        $startDateUpcomingFormatted = $startDateUpcoming->toDateTime()->format('Y-m-d H:i:s');
        $endDateUpcomingFormatted = $endDateUpcoming->toDateTime()->format('Y-m-d H:i:s');
        $startDateExpiredFormatted = $startDateExpired->toDateTime()->format('Y-m-d H:i:s');
        $endDateExpiredFormatted = $endDateExpired->toDateTime()->format('Y-m-d H:i:s');

        if ($request->has('startDate') && $request->has('endDate')) {
            $startDate = Carbon::createFromFormat('d-m-Y', $request->input('startDate'))->startOfDay();
            $endDate = Carbon::createFromFormat('d-m-Y', $request->input('endDate'))->endOfDay();

            $today = now()->startOfDay();

            $startDateUpcomingFormatted = $today->format('Y-m-d H:i:s');
            $endDateUpcomingFormatted   = $endDate->format('Y-m-d H:i:s');
            $startDateExpiredFormatted  = $startDate->format('Y-m-d H:i:s');
            $endDateExpiredFormatted    = now()->subDay()->endOfDay()->format('Y-m-d H:i:s');
        }
        
        // Query for upcoming renewals
        $upcomingMatchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $startDateUpcomingFormatted,
                    '$lt' => $endDateUpcomingFormatted,
                ],
            ],
        ];

        $upcomingGroupStage = [
            '$group' => [
                '_id' => '$trace_id',
                'proposer_mobile' => ['$first' => '$proposer_mobile'],
                'seller_name' => ['$first' => '$seller_name'],
                'vehicle_registration_number' => ['$first' => '$vehicle_registration_number'],
                'lob' => ['$first' => '$section'],
                'sum_assured' => ['$first' => '$sum_assured'],
                'proposer_name' => ['$first' => '$proposer_name'],
                'company_name' => ['$first' => '$company_name'],
                'policy_no' => ['$first' => '$policy_no'],
                'cif_id' => ['$first' => '$cif_id'],
                'policy_end_date' => ['$first' => '$policy_end_date'],
                'business_type' => ['$first' => '$business_type'],
            ],
        ];

        $upcomingSortStage = [
            '$sort' => ['_id' => 1],
        ];

        $upcomingFinalProjectStage = [
            '$project' => [
                'id' => 1,
                'trace_id' => '$_id',
                'proposer_mobile' => 1,
                'seller_name' => 1,
                'vehicle_registration_number' => 1,
                'lob' => 1,
                'sum_assured' => 1,
                'proposer_name' => 1,
                'company_name' => 1,
                'policy_no' => 1,
                '_id' => 0,
                'cif_id' => 1,
                'policy_end_date' => 1,
                'business_type' => 1,
                'status' => 'Upcoming',
            ],
        ];

        // Query for expired renewals
        $expiredMatchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $startDateExpiredFormatted,
                    '$lt' => $endDateExpiredFormatted,
                ],
            ],
        ];

        $expiredGroupStage = [
            '$group' => [
                '_id' => '$trace_id',
                'proposer_mobile' => ['$first' => '$proposer_mobile'],
                'seller_name' => ['$first' => '$seller_name'],
                'vehicle_registration_number' => ['$first' => '$vehicle_registration_number'],
                'lob' => ['$first' => '$section'],
                'sum_assured' => ['$first' => '$sum_assured'],
                'proposer_name' => ['$first' => '$proposer_name'],
                'company_name' => ['$first' => '$company_name'],
                'policy_no' => ['$first' => '$policy_no'],

                'cif_id' => ['$first' => '$cif_id'],
                'policy_end_date' => ['$first' => '$policy_end_date'],
                'business_type' => ['$first' => '$business_type'],
            ],
        ];

        $expiredSortStage = [
            '$sort' => ['_id' => 1],
        ];

        $expiredFinalProjectStage = [
            '$project' => [
                'id' => 1,
                'trace_id' => '$_id',
                'proposer_mobile' => 1,
                'seller_name' => 1,
                'vehicle_registration_number' => 1,
                'lob' => 1,
                'sum_assured' => 1,
                'proposer_name' => 1,
                'company_name' => 1,
                'policy_no' => 1,
                '_id' => 0,
                'cif_id' => 1,
                'policy_end_date' => 1,
                'business_type' => 1,
                'status' => 'Expired',
            ],
        ];

        $upcomingQuery = [
            $upcomingMatchStage,
            $upcomingGroupStage,
            $upcomingSortStage,
            $upcomingFinalProjectStage,
        ];

        $expiredQuery = [
            $expiredMatchStage,
            $expiredGroupStage,
            $expiredSortStage,
            $expiredFinalProjectStage,
        ];

        $upcomingResults = MongoModel::raw(function ($collection) use ($upcomingQuery) {
            return $collection->aggregate($upcomingQuery);
        });

        $expiredResults = MongoModel::raw(function ($collection) use ($expiredQuery) {
            return $collection->aggregate($expiredQuery);
        });

        if ($request->filled('lob')) {

            $upcomingResults = $upcomingResults->where('lob', $request->lob);
            $expiredResults = $expiredResults->where('lob', $request->lob);
        }

        if ($request->filled('search')) {

            $search = $request->search;
            $upcomingResults = collect($upcomingResults);
            $expiredResults = collect($expiredResults);

            $filteredUpcoming = $upcomingResults->filter(function ($item) use ($search) {

                return stripos($item->proposer_mobile ?? '', $search) !== false ||
                    stripos($item->seller_name ?? '', $search) !== false ||
                    stripos($item->vehicle_registration_number ?? '', $search) !== false ||
                    stripos($item->lob ?? '', $search) !== false ||
                    stripos($item->proposer_name ?? '', $search) !== false ||
                    stripos($item->company_name ?? '', $search) !== false ||
                    stripos($item->policy_no ?? '', $search) !== false ||
                    stripos($item->trace_id ?? '', $search) !== false ||
                    stripos($item->sum_assured ?? '', $search) !== false;
            })->values();

            $filteredExpired = $expiredResults->filter(function ($item) use ($search) {

                return stripos($item->proposer_mobile ?? '', $search) !== false ||
                    stripos($item->seller_name ?? '', $search) !== false ||
                    stripos($item->vehicle_registration_number ?? '', $search) !== false ||
                    stripos($item->lob ?? '', $search) !== false ||
                    stripos($item->proposer_name ?? '', $search) !== false ||
                    stripos($item->company_name ?? '', $search) !== false ||
                    stripos($item->policy_no ?? '', $search) !== false ||
                    stripos($item->trace_id ?? '', $search) !== false ||
                    stripos($item->sum_assured ?? '', $search) !== false;
            })->values();

            return response()->json([
                'status' => 200,
                'column_head' => $columnHead,
                'return_data' => [
                    'upcoming' => $filteredUpcoming ?? null,
                    'expired' => $filteredExpired ?? null,
                ],
                'message' => 'Records Found',
            ]);
        }

        if ($request->filled('export') && $request->export == true) {
            if (! $auth->can($uploadPermission)) {
                return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
            }
            $upcomingResults = $upcomingResults->toArray();
            $expiredResults = $expiredResults->toArray();

            $mergedArray = array_merge($upcomingResults, $expiredResults);

            $data = collect($mergedArray)->map(function ($item) {
                return [
                    'proposer_name' => $item['proposer_name'] ?? '',
                    'proposer_mobile' => $item['proposer_mobile'] ?? '',
                    'vehicle_registration_number' => $item['vehicle_registration_number'] ?? '',
                    'sum_assured' => $item['sum_assured'] ?? '',
                    'company_name' => $item['company_name'] ?? '',
                    'policy_no' => $item['policy_no'] ?? '',
                    'trace_id' => $item['trace_id'] ?? '',
                    'seller_name' => $item['seller_name'] ?? '',
                    'lob' => $item['lob'] ?? '',
                    'cif_id' => $item['cif_id'] ?? '',
                    'policy_end_date' => $item['policy_end_date'] ?? '',
                ];
            })->values()->toArray();

            $filePath = 'exports/Renewal_Data.xlsx';
            Excel::store(new RenewalDataExport($data), $filePath, 'public');
            $downloadLink = Storage::url($filePath);

            return response()->json([
                'success' => true,
                'download_link' => url($downloadLink),
            ]);
        }

        $renewalPopupFlag = config('renewal_redirect_popup_flag') === "true";

        $icLobMap = [];

        if ($renewalPopupFlag) {
            $icLobMap = DB::table('renewals_ic_names')
                ->select('company_name', 'lob')
                ->get()
                ->mapWithKeys(function ($row) {
                    return [
                        strtolower(trim($row->company_name)) . '|' . strtoupper(trim($row->lob)) => true
                    ];
                })
                ->toArray();

            $upcomingResults = collect($upcomingResults)->map(function ($item) use ($renewalPopupFlag, $icLobMap) {
                $item['renewal_redirection_modal'] =
                    $this->getRenewalRedirectionModal($item, $renewalPopupFlag, $icLobMap);
    
                return $item;
            })->values();

        $expiredResults = collect($expiredResults)->map(function ($item) use ($renewalPopupFlag, $icLobMap) {
                $item['renewal_redirection_modal'] =
                    $this->getRenewalRedirectionModal($item, $renewalPopupFlag, $icLobMap);
            
                return $item;
        })->values();
        }

        return response()->json([
            'status' => 200,
            'column_head' => $columnHead,
            'return_data' => [
                'upcoming' => $upcomingResults->values(),
                'expired' => $expiredResults->values(),
            ],
            'channel' => $auth->channel,
            'category' => $auth->category,
            'rm_branch_code' => $auth->rm_branch_code,
            'message' => 'Records Found',
        ]);
    }
     
    public function getRenewalRedirectionModal($item, $renewalPopupFlag, $icLobMap)
    {
        if (! $renewalPopupFlag) {
            return null;
        }
    
        $company = strtolower(trim($item['company_name'] ?? ''));
        $lob     = strtoupper(trim($item['lob'] ?? ''));
    
        if ($company && $lob) {
            $key = $company . '|' . $lob;
    
            if (isset($icLobMap[$key])) {
                return 1;
            }
        }
    
        return 2;
    }

    public function renewalTrendOldest(Request $request)
    {
        $sections = [];
        $sellerTypeAgg = $this->getUserhierarchy($request);

        $lob = $request->input('lob');
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $sections = [$lob];
        } else {
            $lobQuery = $this->AllLobs();

            foreach ($lobQuery as $value) {
                $sections[] = $value['lob'];
            }
        }

        $transactionStages = $this->transactionStagesQuery();

        // Dates for upcoming renewals
        $startDateUpcoming = new UTCDateTime(now()->startOfDay()->getTimestamp() * 1000);
        $endDateUpcoming = new UTCDateTime(now()->addMonth()->startOfDay()->getTimestamp() * 1000);

        // Dates for expired renewals
        $startDateExpired = new UTCDateTime(now()->subDays(30)->startOfDay()->getTimestamp() * 1000);
        $endDateExpired = new UTCDateTime(now()->subDay()->startOfDay()->getTimestamp() * 1000);

        $startDateRenewed = new UTCDateTime(now()->subDays(180)->startOfDay()->getTimestamp() * 1000);
        $endDateRenewed = new UTCDateTime(now()->addMonth()->startOfDay()->getTimestamp() * 1000);

        // Format dates
        $startDateUpcomingFormatted = $startDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateUpcomingFormatted = $endDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $startDateExpiredFormatted = $startDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateExpiredFormatted = $endDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $startDateRenewedFormatted = $startDateRenewed->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateRenewedFormatted = $endDateRenewed->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');

        // Query for upcoming renewals

        $match = [
            '$or' => $sellerTypeAgg,
            'section' => ['$in' => $sections],
            'transaction_stage' => ['$in' => $transactionStages],
            'policy_end_date' => [
                '$gte' => $startDateUpcomingFormatted,
                '$lt' => $endDateUpcomingFormatted,
            ],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    $match['broker_'.$key] = $value;
                }
            }
        }

        $upcomingMatchStage = [
            '$match' => $match,
        ];

        $upcomingGroupStage = [
            '$group' => [
                '_id' => null,
                'total_policies' => ['$sum' => 1],
            ],
        ];

        $upcomingSortStage = [
            '$sort' => ['count' => -1],
        ];

        $upcomingFinalProjectStage = [
            '$project' => [
                '_id' => 0,
                'total_policies' => 1,
            ],
        ];

        // Query for expired renewals
        $expiredMatchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $startDateExpiredFormatted,
                    '$lt' => $endDateExpiredFormatted,
                ],
            ],
        ];

        $expiredGroupStage = [
            '$group' => [
                '_id' => null,
                'total_policies' => ['$sum' => 1],
            ],
        ];

        $expiredSortStage = [
            '$sort' => ['count' => -1],
        ];

        $expiredFinalProjectStage = [
            '$project' => [
                '_id' => 0,
                'total_policies' => 1,
            ],
        ];

        // Renewed stage
        $renewedMatchStage = [
            '$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                // 'is_renewal' => 'Y',
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_start_date' => [
                    '$gte' => $startDateRenewedFormatted,
                    '$lt' => $endDateRenewedFormatted,
                ],
            ],
        ];

        $renewedGroupStage = [
            '$group' => [
                '_id' => null,
                'total_policies' => ['$sum' => 1],
            ],
        ];

        $renewedSortStage = [
            '$sort' => ['count' => -1],
        ];

        $renewedFinalProjectStage = [
            '$project' => [
                '_id' => 0,
                'total_policies' => 1,
            ],
        ];
        // end

        $upcomingQuery = [
            $upcomingMatchStage,
            $upcomingGroupStage,
            $upcomingSortStage,
            $upcomingFinalProjectStage,
        ];

        $expiredQuery = [
            $expiredMatchStage,
            $expiredGroupStage,
            $expiredSortStage,
            $expiredFinalProjectStage,
        ];

        $renewedQuery = [
            $renewedMatchStage,
            $renewedGroupStage,
            $renewedSortStage,
            $renewedFinalProjectStage,
        ];

        // dd($upcomingQuery);

        $dueQuery = MongoModel::raw(fn ($collection) => $collection->aggregate($upcomingQuery))->toArray();
        $expiredResults = MongoModel::raw(fn ($collection) => $collection->aggregate($expiredQuery))->toArray();
        $renewedQuery = MongoModel::raw(fn ($collection) => $collection->aggregate($renewedQuery))->toArray();

        $dueResult = $dueQuery[0]['total_policies'] ?? 0;
        $renewedResult = $renewedQuery[0]['total_policies'] ?? 0;
        $rolloverResult = $renewedQuery[0]['total_policies'] ?? 0;
        $total = $dueResult + $renewedResult + $rolloverResult;

        $duePercentage = $total > 0 ? round(($dueResult / $total) * 100, 1) : 0;
        $renewedPercentage = $total > 0 ? round(($renewedResult / $total) * 100, 1) : 0;
        $rolloverPercentage = $total > 0 ? round(($rolloverResult / $total) * 100, 1) : 0;

        $Renewals_Split = [
            [
                'name' => 'Due',
                'value' => $dueResult,
                'percentage' => $duePercentage,
            ],
            [
                'name' => 'Rollover',
                'value' => $rolloverResult,
                'percentage' => $rolloverPercentage,
            ],
            [
                'name' => 'Renewed',
                'value' => $renewedResult,
                'percentage' => $renewedPercentage,
            ],
        ];

        $totalConvert = $renewedResult + $dueResult;
        $totalConvertPercent = $totalConvert > 0 ? round(($renewedResult / $totalConvert) * 100, 1) : 0;

        $conversion_rate = [
            [
                'renewed' => $renewedResult,
                'due' => $dueResult,
                'percentage' => $totalConvertPercent,
            ],
        ];

        return response()->json([
            'status' => 200,
            'return_data' => [
                'Renewals_Split' => $Renewals_Split,
                'Conversion_Rate' => $conversion_rate,
            ],
            'message' => 'Records Found',
        ]);
    }

    public function renewalTrendNew(Request $request)
    {
        // --------------- INPUTS -----------------

        $sellerTypeAgg = $this->getUserhierarchy($request);

        $lob = $request->input('lob');
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $sections = [$lob];
        } else {
            $lobQuery = $this->AllLobs();

            foreach ($lobQuery as $value) {
                $sections[] = $value['lob'];
            }
        }

        $transactionStages = $this->transactionStagesQuery();

        $startDate = Carbon::createFromFormat('d-m-Y', $request->startDate)->startOfDay();
        $endDate = Carbon::createFromFormat('d-m-Y', $request->endDate)->endOfDay();
        $year = (int) $request->year;

        // Year range for Renewal Trend
        $yearStart = Carbon::create($year, 1, 1)->startOfDay();
        $yearEnd = Carbon::create($year, 12, 31)->endOfDay();

        // Dates for upcoming renewals
        $startDateUpcoming = new UTCDateTime($startDate->startOfDay()->getTimestamp() * 1000);
        $endDateUpcoming = new UTCDateTime($endDate->addMonth()->startOfDay()->getTimestamp() * 1000);

        // Dates for expired renewals
        $startDateExpired = new UTCDateTime($startDate->subDays(30)->startOfDay()->getTimestamp() * 1000);
        $endDateExpired = new UTCDateTime($endDate->subDay()->startOfDay()->getTimestamp() * 1000);

        $startDateRenewed = new UTCDateTime($startDate->subDays(180)->startOfDay()->getTimestamp() * 1000);
        $endDateRenewed = new UTCDateTime($endDate->addMonth()->startOfDay()->getTimestamp() * 1000);

        // Format dates
        $startDateUpcomingFormatted = $startDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateUpcomingFormatted = $endDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $startDateExpiredFormatted = $startDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateExpiredFormatted = $endDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $startDateRenewedFormatted = $startDateRenewed->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateRenewedFormatted = $endDateRenewed->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');

        // -----------------------------------------
        // PIPELINE A: Renewed Count (Group by month)
        // -----------------------------------------
        $renewedPipeline = [
            ['$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_start_date' => [
                    '$gte' => $yearStart,
                    '$lt' => $yearEnd,
                ],
            ]],
            ['$group' => [
                '_id' => ['month' => ['$month' => '$policy_start_date']],
                'renewed' => ['$sum' => 1],
            ]],
            ['$project' => [
                '_id' => 0,
                'month' => '$_id.month',
                'renewed' => 1,
            ]],
            ['$sort' => ['month' => 1]],
        ];

        // -----------------------------------------
        // PIPELINE B: Due Count (Group by month)
        // -----------------------------------------
        $lostPipeline = [
            ['$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $startDateExpiredFormatted,
                    '$lt' => $endDateExpiredFormatted,
                ],
            ]],
            ['$group' => [
                '_id' => ['month' => ['$month' => '$policy_end_date']],
                'lost' => ['$sum' => 1],
            ]],
            ['$project' => [
                '_id' => 0,
                'month' => '$_id.month',
                'lost' => 1,
            ]],
            ['$sort' => ['month' => 1]],
        ];

        // Run Aggregations
        $renewedData = MongoModel::raw(fn ($c) => $c->aggregate($renewedPipeline))->toArray();
        $lostData = MongoModel::raw(fn ($c) => $c->aggregate($lostPipeline))->toArray();

        // -----------------------------------------
        // BUILD MONTH-WISE TREND (12 months)
        // -----------------------------------------
        $monthLabels = [
            1 => 'Jan', 2 => 'Feb', 3 => 'Mar', 4 => 'Apr', 5 => 'May', 6 => 'Jun',
            7 => 'Jul', 8 => 'Aug', 9 => 'Sep', 10 => 'Oct', 11 => 'Nov', 12 => 'Dec',
        ];

        $renewalTrend = [];

        foreach ($monthLabels as $num => $label) {
            $renewed = collect($renewedData)->firstWhere('month', $num)['renewed'] ?? 0;
            $lost = collect($lostData)->firstWhere('month', $num)['lost'] ?? 0;

            $renewalTrend[] = [
                'month' => $label,
                'renewed' => $renewed,
                'lost' => $lost,
            ];
        }

        // -----------------------------------------
        // RENEWALS SPLIT (Due, Rollover, Renewed)
        // -----------------------------------------
        $dueCount = array_sum(array_column($lostData, 'lost'));
        $renewedCount = array_sum(array_column($renewedData, 'renewed'));

        // Example: Rollover = Due but not lost? (Adjust your logic)
        $rolloverCount = max($dueCount - $renewedCount, 0);

        $total = $dueCount + $rolloverCount + $renewedCount;

        $renewalSplit = [
            [
                'name' => 'Due',
                'value' => $dueCount,
                'percentage' => $total ? round(($dueCount / $total) * 100, 1) : 0,
            ],
            [
                'name' => 'Rollover',
                'value' => $rolloverCount,
                'percentage' => $total ? round(($rolloverCount / $total) * 100, 1) : 0,
            ],
            [
                'name' => 'Renewed',
                'value' => $renewedCount,
                'percentage' => $total ? round(($renewedCount / $total) * 100, 1) : 0,
            ],
        ];

        // -----------------------------------------
        // Conversion Rate
        // -----------------------------------------
        $totalConvert = $renewedCount + $dueCount;
        $conversionRate = [
            [
                'renewed' => $renewedCount,
                'due' => $dueCount,
                'percentage' => $totalConvert > 0 ? round(($renewedCount / $totalConvert) * 100, 1) : 0,
            ],
        ];

        // -----------------------------------------
        // FINAL RESPONSE
        // -----------------------------------------
        return response()->json([
            'status' => 200,
            'return_data' => [
                'Renewals_Split' => $renewalSplit,
                'Renewal_Trend' => $renewalTrend,
                'conversionRate' => $conversionRate,
            ],
            'message' => 'Records Found',
        ]);
    }

    public function renewalTrend(Request $request)
    {
        // --------------- INPUTS -----------------

        $year = (int) ($request->year ?? now()->year);

        // Year range for Renewal Trend
        if ($request->has('startDate')) {
            $startDate = Carbon::parse($request->startDate)->startOfDay();
            $endDate = Carbon::parse($request->endDate)->endOfDay();

            // Dates for upcoming renewals
            $startDateUpcoming = new UTCDateTime($startDate->startOfDay()->getTimestamp() * 1000);
            $endDateUpcoming = new UTCDateTime($endDate->endOfDay()->getTimestamp() * 1000);

            // Dates for expired renewals
            $startDateExpired = new UTCDateTime($startDate->subDays(30)->startOfDay()->getTimestamp() * 1000);
            $endDateExpired = new UTCDateTime($endDate->subDay()->startOfDay()->getTimestamp() * 1000);

        }else{
            // Dates for upcoming renewals
            $startDateUpcoming = new UTCDateTime(now()->startOfDay()->getTimestamp() * 1000);
            $endDateUpcoming = new UTCDateTime(now()->addMonth()->startOfDay()->getTimestamp() * 1000);

            // Dates for expired renewals
            $startDateExpired = new UTCDateTime(now()->subDays(30)->startOfDay()->getTimestamp() * 1000);
            $endDateExpired = new UTCDateTime(now()->subDay()->startOfDay()->getTimestamp() * 1000);

        }
        $yearStart = Carbon::create($year, 1, 1)->startOfDay();
        $yearEnd = Carbon::create($year, 12, 31)->endOfDay();

        // Format dates
        $startDateUpcomingFormatted = $startDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateUpcomingFormatted = $endDateUpcoming->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $startDateExpiredFormatted = $startDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        $endDateExpiredFormatted = $endDateExpired->toDateTime()->setTimezone(new DateTimeZone('Asia/Kolkata'))->format('Y-m-d H:i:s');
        

        $sellerTypeAgg = $this->getUserhierarchy($request);

        $lob = $request->input('lob');
        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $sections = [$lob];
        } else {
            $lobQuery = $this->AllLobs();

            foreach ($lobQuery as $value) {
                $sections[] = $value['lob'];
            }
        }

        $transactionStages = $this->transactionStagesQuery();

        // Renewed Count (Group by month)
        $renewedPipeline = [
            ['$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'is_renewed'=>'Y', // consider only renewed policies
                'policy_start_date' => [
                    '$gte' => $yearStart,
                    '$lt' => $yearEnd,
                ],
            ]],
            ['$group' => [
                '_id' => ['month' => ['$month' => '$policy_start_date']],
                'renewed' => ['$sum' => 1],
            ]],
            ['$project' => [
                '_id' => 0,
                'month' => '$_id.month',
                'renewed' => 1,
            ]],
            ['$sort' => ['month' => 1]],
        ];

        // Lost Count (Group by month)
        $lostPipeline = [
            ['$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $yearStart,
                    '$lt' => $yearEnd,
                ],
            ]],
            ['$group' => [
                '_id' => ['month' => ['$month' => '$policy_end_date']],
                'lost' => ['$sum' => 1],
            ]],
            ['$project' => [
                '_id' => 0,
                'month' => '$_id.month',
                'lost' => 1,
            ]],
            ['$sort' => ['month' => 1]],
        ];

        // Run Aggregations
        $renewedData = MongoModel::raw(fn ($c) => $c->aggregate($renewedPipeline))->toArray();
        $lostData = MongoModel::raw(fn ($c) => $c->aggregate($lostPipeline))->toArray();

        // -----------------------------------------
        // BUILD MONTH-WISE TREND (12 months)
        // -----------------------------------------
        $monthLabels = [
            1 => 'Jan', 2 => 'Feb', 3 => 'Mar', 4 => 'Apr', 5 => 'May', 6 => 'Jun',
            7 => 'Jul', 8 => 'Aug', 9 => 'Sep', 10 => 'Oct', 11 => 'Nov', 12 => 'Dec',
        ];

        $renewalTrend = [];

        foreach ($monthLabels as $num => $label) {
            $renewed = collect($renewedData)->firstWhere('month', $num)['renewed'] ?? rand(1, 100);
            $lost = collect($lostData)->firstWhere('month', $num)['lost'] ?? rand(1, 100);

            $renewalTrend[] = [
                'month' => $label,
                'renewed' => $renewed,
                'lost' => $lost,
            ];
        }

        // -----------------------------------------
        // RENEWALS SPLIT (Due, Rollover, Renewed)
        // -----------------------------------------

        // Upcoming renewals query
        $upcomingPipeline = [
            ['$match' => [
                '$or' => $sellerTypeAgg,
                'section' => ['$in' => $sections],
                'transaction_stage' => ['$in' => $transactionStages],
                'policy_end_date' => [
                    '$gte' => $startDateUpcomingFormatted,
                    '$lt' => $endDateUpcomingFormatted,
                ],
            ]],
            ['$group' => [
                '_id' => '$section',
                'count' => ['$sum' => 1],
            ]],
            ['$project' => [
                'id' => ['$add' => [1, ['$indexOfArray' => ['$section', '$_id']]]],
                'lob' => '$_id',
                'count' => 1,
                '_id' => 0,
            ]],
            ['$sort' => ['count' => -1]],
        ];

        $upcomingData = MongoModel::raw(fn ($c) => $c->aggregate($upcomingPipeline))->toArray();
        
        $lostCount = array_sum(array_column($lostData, 'lost')) > 0 ? array_sum(array_column($lostData, 'lost')) : rand(1, 100);
        $renewedCount = array_sum(array_column($renewedData, 'renewed')) > 0 ? array_sum(array_column($renewedData, 'renewed')) : rand(1, 100);
        $upcomingCount = array_sum(array_column($upcomingData, 'upcoming')) > 0 ? array_sum(array_column($upcomingData, 'upcoming')) : rand(1, 100);

        $total = $upcomingCount + $renewedCount;

        $renewalSplit = [
            [
                'name' => 'Due',
                'value' => $upcomingCount,
                'percentage' => $total ? round(($upcomingCount / $total) * 100, 1) : 20,
            ],
            [
                'name' => 'Renewed',
                'value' => $renewedCount,
                'percentage' => $total ? round(($renewedCount / $total) * 100, 1) : 50,
            ],
        ];

        // -----------------------------------------
        // Conversion Rate
        // -----------------------------------------
        $totalConvert = $renewedCount + $upcomingCount;
        $conversionRate = [
            [
                'renewed' => $renewedCount > 0 ? $renewedCount : 5,
                'due' => $upcomingCount > 0 ? $upcomingCount : 10,
                'percentage' => $totalConvert > 0 ? round(($renewedCount / $totalConvert) * 100, 1) : 70,
            ],
        ];

        // -----------------------------------------
        // FINAL RESPONSE
        // -----------------------------------------
        return response()->json([
            'status' => 200,
            'return_data' => [
                'Renewals_Split' => $renewalSplit,
                'Renewal_Trend' => $renewalTrend,
                'Conversion_Rate' => $conversionRate,
            ],
            'message' => 'Records Found',
        ]);
    }

    public function overAllConversionRate(Request $request)
    {
        $sellerTypeAgg = $this->dataFlagCheck($request);
        $lobData = $this->AllLobs();
        $lobs = array_column($lobData, 'lob');
        $transactionStages = $this->transactionStagesQuery();

        $startDate = $request->input('start_date');
        $endDate = $request->input('end_date');
        $lob = $request->input('lob');

        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $lobs = [$lob];
        } else {
            $lobs = array_column($lobData, 'lob');
        }

        $matchConditions = [
            '$and' => [
                ['$or' => $sellerTypeAgg ],
                ['section' => ['$in' => $lobs]],
                ['trace_id' => ['$exists' => true, '$ne' => null]]
            ]
        ];

        if ($startDate && $endDate) {
            $startDateFormatted = date('Y-m-d H:i:s', strtotime($startDate.' 00:00:00'));
            $endDateFormatted = date('Y-m-d H:i:s', strtotime($endDate.' 23:59:59'));

            $matchConditions['$and'][] = [
                'lastupdated_time' => [
                    '$gte' => $startDateFormatted,
                    '$lte' => $endDateFormatted,
                ]
            ];
        }

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();
        
            if (!empty($utmParameter)) {
        
                $utmOr = [];
        
                foreach ($utmParameter as $key => $value) {
        
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }
        
                    $brokerKey = 'broker_' . $key;
        
                    $valueArr = explode(',', $value);
        
                    if (count($valueArr) > 1) {
                        $utmOr[] = [
                            $brokerKey => ['$in' => $valueArr]
                        ];
                    } else {
                        $utmOr[] = [
                            $brokerKey => $value
                        ];
                    }
                }
 
                if (!empty($utmOr)) {
                    $matchConditions['$and'][] = ['$or' => $utmOr];
                }
            }
        }

        $matchStage = [
            '$match' => $matchConditions,
        ];

        $groupStage = [
            '$group' => [
                '_id' => '$section',
                'totalTraceIds' => ['$sum' => 1],
                'issuedPolicies' => [
                    '$sum' => [
                        '$cond' => [
                            ['$in' => ['$transaction_stage', $transactionStages]],
                            1,
                            0,
                        ],
                    ],
                ],
            ],
        ];

        $addFieldsStage = [
            '$addFields' => [
                'conversionRatePercent' => [
                    '$cond' => [
                        ['$gt' => ['$totalTraceIds', 0]],
                        [
                            '$concat' => [
                                [
                                    '$toString' => ['$multiply' => [['$divide' => ['$issuedPolicies', '$totalTraceIds']],100,],]
                                    // [
                                        // '$round' => [
                                        //     [
                                                // '$multiply' => [['$divide' => ['$issuedPolicies', '$totalTraceIds']],100,],
                                        //     ],
                                        //     2,
                                        // ],
                                    // ],
                                ],
                                '%',
                            ],
                        ],
                        '0%',
                    ],
                ],
            ],
        ];

        $projectStage = [
            '$project' => [
                '_id' => 0,
                'section' => '$_id',
                'totalTraceIds' => 1,
                'issuedPolicies' => 1,
                'conversionRatePercent' => 1,
            ],
        ];

        $pipeline = [$matchStage, $groupStage, $addFieldsStage, $projectStage];

        $results = MongoModel::raw(function ($collection) use ($pipeline) {
            return $collection->aggregate($pipeline);
        })->toArray();

        $totalTraceIds = 0;
        $totalIssuedPolicies = 0;

        foreach ($results as $res) {
            $totalTraceIds += $res['totalTraceIds'] ?? 0;
            $totalIssuedPolicies += $res['issuedPolicies'] ?? 0;
        }

        $conversionRate = $totalTraceIds > 0
            ? round(($totalIssuedPolicies / $totalTraceIds) * 100, 2).'%'
            : '0%';

        return response()->json([
            'status' => 200,
            'return_data' => [
                'totalTraceIds' => $totalTraceIds,
                'totalIssuedPolicies' => $totalIssuedPolicies,
                'overallconversionRatePercent' => $conversionRate,
                'lobWiseTraceIdCount' => $results,
            ],
            'message' => 'Counts and conversion rate fetched successfully',
        ]);
    }

    public function lobWiseTraceidList(Request $request)
    {
        $sellerTypeAgg = $this->getUserhierarchy($request);
        $transactionStages = $this->transactionStagesQuery();
        $lobData = $this->AllLobs();
        $validLobs = array_column($lobData, 'lob');

        $requestedLob = $request->input('lob');
        $search = $request->input('search');
        $startDate = $request->input('start_date');
        $endDate = $request->input('end_date');
        $type = $request->input('type'); // either 'visitors_trace_ids' or 'issued_policies'
        $page = (int) $request->input('page', 1);
        $perPage = (int) $request->input('size', 10);

        if (! $requestedLob || ! in_array($requestedLob, $validLobs)) {
            return response()->json([
                'status' => 400,
                'message' => 'Invalid or missing LOB value.',
            ]);
        }

        $matchConditions = [
            '$or' => $sellerTypeAgg,
            'section' => $requestedLob,
            'trace_id' => ['$exists' => true, '$ne' => null],
        ];

        if ($startDate && $endDate) {
            $matchConditions['lastupdated_time'] = [
                '$gte' => date('Y-m-d H:i:s', strtotime($startDate.' 00:00:00')),
                '$lte' => date('Y-m-d H:i:s', strtotime($endDate.' 23:59:59')),
            ];
        }

        if ($search) {
            $regex = new \MongoDB\BSON\Regex($search, 'i');
            $matchConditions['trace_id'] = $regex;
        }

        $pipeline = [
            ['$match' => $matchConditions],
            ['$project' => [
                '_id' => 0,
                'trace_id' => 1,
                'transaction_stage' => 1,
                'proposer_name' => 1,
                'proposer_mobile' => 1,
                'proposer_emailid' => 1,
                'lastupdated_time' => 1,
                'policy_start_date' => 1,
                'policy_end_date' => 1,
                'policy_no' => 1,
                'policy_doc_path' => 1,
            ]],
        ];

        $results = MongoModel::raw(fn ($collection) => $collection->aggregate($pipeline))->toArray();

        $traceIds = [];
        $issuedPolicies = [];

        foreach ($results as $doc) {
            $traceIds[] = [
                'trace_id' => $doc['trace_id'],
                'proposer_name' => $doc['proposer_name'] ?? null,
                'proposer_mobile' => $doc['proposer_mobile'] ?? null,
                'proposer_emailid' => $doc['proposer_emailid'] ?? null,
                'lastupdated_time' => $doc['lastupdated_time'] ?? null,
            ];

            if (in_array($doc['transaction_stage'], $transactionStages)) {
                $issuedPolicies[] = [
                    'trace_id' => $doc['trace_id'],
                    'proposer_name' => $doc['proposer_name'] ?? null,
                    'proposer_mobile' => $doc['proposer_mobile'] ?? null,
                    'proposer_emailid' => $doc['proposer_emailid'] ?? null,
                    'lastupdated_time' => $doc['lastupdated_time'] ?? null,
                    'policy_start_date' => $doc['policy_start_date'] ?? null,
                    'policy_end_date' => $doc['policy_end_date'] ?? null,
                    'policy_no' => $doc['policy_no'] ?? null,
                    'policy_doc_path' => $doc['policy_doc_path'] ?? null,
                ];
            }
        }

        $traceIdsPaginated = new LengthAwarePaginator(
            collect($traceIds)->forPage($page, $perPage)->values(),
            count($traceIds),
            $perPage,
            $page,
            ['path' => $request->url(), 'query' => $request->query()]
        );

        $issuedPoliciesPaginated = new LengthAwarePaginator(
            collect($issuedPolicies)->forPage($page, $perPage)->values(),
            count($issuedPolicies),
            $perPage,
            $page,
            ['path' => $request->url(), 'query' => $request->query()]
        );

        if ($type === 'visitors_trace_ids') {
            return response()->json([
                'status' => 200,
                'message' => 'Visitors trace IDs fetched successfully',
                'return_data' => $traceIdsPaginated->items(),
                'pagination' => [
                    'total_records' => $traceIdsPaginated->total(),
                    'size' => $traceIdsPaginated->perPage(),
                    'current_page' => $traceIdsPaginated->currentPage(),
                    'total_pages' => $traceIdsPaginated->lastPage(),
                ],
                'column_head' => [
                    [
                        'header' => 'Trace ID',
                        'accessorKey' => 'trace_id',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Proposer Name',
                        'accessorKey' => 'proposer_name',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Proposer Mobile',
                        'accessorKey' => 'proposer_mobile',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Proposer Email',
                        'accessorKey' => 'proposer_emailid',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Last Updated Time',
                        'accessorKey' => 'lastupdated_time',
                        'type' => 'datetime',
                    ],
                ],
            ]);
        } elseif ($type === 'issued_policies') {
            return response()->json([
                'status' => 200,
                'message' => 'Issued policies fetched successfully',
                'return_data' => $issuedPoliciesPaginated->items(),
                'pagination' => [
                    'total_records' => $issuedPoliciesPaginated->total(),
                    'size' => $issuedPoliciesPaginated->perPage(),
                    'current_page' => $issuedPoliciesPaginated->currentPage(),
                    'total_pages' => $issuedPoliciesPaginated->lastPage(),
                ],
                'column_head' => [
                    [
                        'header' => 'Trace ID',
                        'accessorKey' => 'trace_id',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Proposer Name',
                        'accessorKey' => 'proposer_name',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Proposer Mobile',
                        'accessorKey' => 'proposer_mobile',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Proposer Email',
                        'accessorKey' => 'proposer_emailid',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Last Updated Time',
                        'accessorKey' => 'lastupdated_time',
                        'type' => 'datetime',
                    ],
                    [
                        'header' => 'Policy Start Date',
                        'accessorKey' => 'policy_start_date',
                        'type' => 'date',
                    ],
                    [
                        'header' => 'Policy End Date',
                        'accessorKey' => 'policy_end_date',
                        'type' => 'date',
                    ],
                    [
                        'header' => 'Policy Number',
                        'accessorKey' => 'policy_no',
                        'type' => 'string',
                    ],
                    [
                        'header' => 'Policy Document Path',
                        'accessorKey' => 'policy_doc_path',
                        'type' => 'string',
                    ],
                ],
            ]);
        } else {
            return response()->json([
                'status' => 400,
                'message' => 'Invalid type provided. Use "visitors_trace_ids" or "issued_policies".',
            ]);
        }
    }

    public function crossSellList(Request $request)
    {
        $transactionStages = $this->transactionStagesQuery();
        $sellerTypeAgg = $this->getUserhierarchy($request);

        $requestedSection = $request->input('section');
        $searchMobile = $request->input('mobile');

        $page = (int) $request->input('page', 1);
        $perPage = (int) $request->input('size', 10);

        if (! $requestedSection) {
            return response()->json([
                'status' => 400,
                'message' => 'Missing section parameter.',
            ]);
        }

        $matchConditions = [
            'transaction_stage' => ['$in' => $transactionStages],
            'section' => ['$ne' => $requestedSection],
            '$or' => $sellerTypeAgg,
        ];

        if ($searchMobile) {
            $matchConditions['proposer_mobile'] = $searchMobile;
        }

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (! empty($utmParameter)) {
                foreach ($utmParameter as $key => $value) {
                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $valueArr = explode(',', $value);

                    if (count($valueArr) > 1) {
                        $match['broker_'.$key] = ['$in' => $valueArr];
                    } else {
                        $match['broker_'.$key] = $value;
                    }
                }
            }
        }

        $records = MongoModel::raw(function ($collection) use ($matchConditions) {
            return $collection->find($matchConditions, [
                'projection' => [
                    'trace_id' => 1,
                    'proposer_name' => 1,
                    'proposer_mobile' => 1,
                    'proposer_email' => 1,
                    'section' => 1,
                    'transaction_stage' => 1,
                    'policy_no' => 1,
                ],
            ]);
        });

        $recordsArray = iterator_to_array($records);

        $grouped = [];
        foreach ($recordsArray as $record) {
            $mobile = $record['proposer_mobile'] ?? null;
            if ($mobile) {
                $grouped[$mobile][] = $record;
            }
        }

        $filtered = [];
        foreach ($grouped as $mobile => $entries) {
            if (count($entries) >= 1) {
                $filtered[] = [
                    'proposer_mobile' => $mobile,
                    'policies' => $entries,
                ];
            }
        }

        $flatData = [];
        foreach ($filtered as $item) {
            foreach ($item['policies'] as $policy) {
                $flatData[] = [
                    'Trace ID' => isset($policy['trace_id']) ? "{$policy['trace_id']}'" : '',
                    'Proposer Mobile' => $item['proposer_mobile'],
                    'Proposer Name' => $policy['proposer_name'] ?? '',
                    'Proposer Email' => $policy['proposer_email'] ?? '',
                    'Section' => $policy['section'] ?? '',
                    'Transaction Stage' => $policy['transaction_stage'] ?? '',
                    'Policy No' => isset($policy['policy_no']) ? "{$policy['policy_no']}'" : '',
                ];
            }
        }

        if ($request->input('export', false)) {
            $dataCount = count($flatData);
            $maxAllowedCount = config('excel.data.limit.download');
            $headings = ['Trace ID', 'Proposer Mobile', 'Proposer Name', 'Proposer Email', 'Section', 'Transaction Stage', 'Policy No'];

            if ($dataCount > $maxAllowedCount) {
                ExcelDownloadLog::insert([
                    'user_id' => Auth::id(),
                    'request' => json_encode($request->all()),
                    'status' => '0',
                    'created_at' => Carbon::now(),
                    'source' => 'CrossSellList Data Export',
                ]);

                $filename = 'CrossSellList'.rand(1, 10000000).'.xlsx';

                ExportLargeExcel::dispatch(
                    $flatData,
                    $headings,
                    $request->all(),
                    Auth::id(),
                    'CrossSellListDataExport',
                    $filename
                )->onQueue('LargeExcelExports');

                return response()->json([
                    'status' => 200,
                    'message' => 'Data is too large to download. Added to queue; you will get this file later in the job list.',
                ]);
            } else {
                $fileName = 'CrossSellList/'.Str::random(10).'.xlsx';
                $export = new CrossSellListDataExport($flatData, $headings);
                Excel::store($export, $fileName, 'public');

                $downloadLink = Storage::disk('public')->url($fileName);

                return response()->json([
                    'status' => 200,
                    'message' => 'Excel file generated successfully',
                    'link' => $downloadLink,
                ]);
            }
        }

        $paginated = new LengthAwarePaginator(
            collect($flatData)->forPage($page, $perPage)->values(),
            count($flatData),
            $perPage,
            $page,
            ['path' => $request->url(), 'query' => $request->query()]
        );

        return response()->json([
            'status' => 200,
            'message' => 'Mobiles with policies fetched successfully',
            'return_data' => $paginated->items(),
            'pagination' => [
                'total_records' => $paginated->total(),
                'size' => $paginated->perPage(),
                'current_page' => $paginated->currentPage(),
                'total_pages' => $paginated->lastPage(),
            ],
        ]);
    }

    public function topEmployee(Request $request)
    {
        $user = Auth::user();
        if ($user->usertype == 1) {
            $sellerdata = getUserChildren($user, $user->usertype);
            if (! $sellerdata) {
                return response()->json([
                    'status' => 500,
                    'message' => 'NO seller data found.',
                ]);
            }
            $issueStage = $this->transactionStagesQuery();
            $seller_id = array_column($sellerdata, 'id');
            $result = MongoModel::raw(function ($collection) use ($seller_id, $issueStage) {
                return $collection->aggregate([
                    [
                        '$match' => [
                            'seller_id' => ['$in' => $seller_id],
                            'transaction_stage' => ['$in' => $issueStage],
                        ],
                    ],
                    [
                        '$group' => [
                            '_id' => '$seller_id',
                            'Premium' => ['$sum' => '$premium_amount'],
                            'seller_name' => ['$first' => '$seller_name'],
                            'seller_mobile' => ['$first' => '$seller_mobile'],
                            'Policies' => ['$sum' => 1],
                        ],
                    ],
                    [
                        '$sort' => ['Premium' => -1],
                    ],
                    // [
                    //     '$limit' => 10
                    // ],
                ]);
            });

            if ($result->isEmpty()) {
                return response()->json([
                    'success' => false,
                    'message' => 'No matching data found',
                    'data' => [],
                ], 404);
            }
            $result = $result->map(function ($row, $index) {
                $row['sr_no'] = $index + 1;

                return $row;
            });

            return response()->json([
                'status' => 200,
                'column_head' => [
                    [
                        'header' => 'Sr.No',
                        'accessorKey' => 'sr_no',
                    ],
                    [
                        'header' => 'Seller Name',
                        'accessorKey' => 'seller_name',
                    ],
                    [
                        'header' => 'Seller Mobile',
                        'accessorKey' => 'seller_mobile',
                    ],
                    [
                        'header' => 'Policies',
                        'accessorKey' => 'Policies',
                    ],
                    [
                        'header' => 'Premium Amount',
                        'accessorKey' => 'premium_amount',
                    ],
                ],
                'data' => $result,
            ]);
        } else {
            return response()->json([
                'status' => 500,
                'message' => 'Not an employee.',

            ]);
        }
    }

    public function topRanking(Request $request)
    {
        set_time_limit(0);
        ini_set('memory_limit','-1');
        $user = Auth::user();
        $seller_id = [];
        $startDate = $request->startDate ? Carbon::parse($request->startDate)->startOfDay() : null;
        $endDate = $request->endDate ? Carbon::parse($request->endDate)->endOfDay() : null;

        if ($user->usertype == 1 && $user->is_admin == 'Y') {
            $seller_data_id = User::get(['id', 'usertype', 'employee_code','name','middle_name','last_name','mobile'])
                ->mapWithKeys(function ($item) {
                    return [
                        $item->id => [
                            'usertype' => $item->usertype,
                            'employee_code' => $item->employee_code,
                            'name' => credential_decrypt($item->name),
                            'middle_name' => credential_decrypt($item->middle_name),
                            'last_name' => credential_decrypt($item->last_name),
                            'mobile' => credential_decrypt($item->mobile)
                        ]
                    ];
                })
                ->toArray();
            $seller_id = array_keys($seller_data_id);
            $seller_data_employee_code = User::whereIn('usertype',[1,7])->distinct()->get(['usertype', 'employee_code','name','middle_name','last_name','mobile'])
                ->mapWithKeys(function ($item) {
                    return [
                        $item->employee_code => [
                            'usertype' => $item->usertype,
                            'employee_code' => $item->employee_code,
                            'name' => credential_decrypt($item->name),
                            'middle_name' => credential_decrypt($item->middle_name),
                            'last_name' => credential_decrypt($item->last_name),
                            'mobile' => credential_decrypt($item->mobile)
                        ]
                    ];
                })
                ->toArray();
                $seller_employee_code = array_map(
                    fn($code) => "'".$code."'",
                    array_keys($seller_data_employee_code)
                );
        } elseif ($user->usertype == 2 && $user->is_admin == 'Y') {
            $seller_id = User::where('usertype', 2)->pluck('id')->toArray();
        } elseif ($user->usertype == 3 && $user->is_admin == 'Y') {
            $seller_id = User::where('usertype', 3)->pluck('id')->toArray();
        } else {
            if ($user->usertype == 3 && $user->is_admin == 'N') {
                $seller_id = array_column(getUserChildren($user, $user->usertype), 'id');
                $seller_id[] = $user->id;
            } elseif ($user->usertype == 2 && $user->is_admin == 'N') {
                $seller_id = array_column(getUserChildren($user, $user->usertype), 'id');
                $seller_id[] = $user->id;
            } elseif ($user->usertype == 1 && $user->is_admin == 'N') {
                $hierarchyData = getUserLowerHierarchy($user->id, $user->usertype);
                if (! $hierarchyData) {
                    return response()->json([
                        'status' => 500,
                        'message' => 'NO seller data found.',
                    ]);
                }
                $UserIdentifier = getUserTypeFromToken();
                $usersIdWithTypetoFetch = [
                    $UserIdentifier => array_column($hierarchyData, 'id'),
                ];
                $allemployeedata = array_column($hierarchyData, 'employee_code');
                $allemployeedata[] = $user->employee_code;
                $usersIdWithTypetoFetch[$UserIdentifier] = array_merge($usersIdWithTypetoFetch[$UserIdentifier], [$user->id]);

                if ($user->usertype == 1) {
                    $finalMappingData = getMapPosPartner($allemployeedata);
                    $finalpospartnerdata = collect($finalMappingData)
                        ->groupBy('usertype')
                        ->mapWithKeys(function ($group, $key) {
                            return [
                                $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck('id')->all(),
                            ];
                        })
                        ->toArray();
                    if (! empty($finalpospartnerdata)) {
                        $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                    }
                }
                $seller_id = collect($usersIdWithTypetoFetch)->flatten()->toArray();
            }
        }
        $issueStage = $this->transactionStagesQuery();

        $match = [
            '$or' => [
                ['seller_id' => ['$in' => $seller_id]],
                ['RmCode' => ['$in' => $seller_employee_code]]
            ],
            'transaction_stage' => ['$in' => $issueStage],
            'seller_name' => ['$nin' => ['', null, 'N/A']],
        ];

        if (!empty($startDate) && !empty($endDate)) {
            $match['lastupdated_time'] = [
                '$gte' => $startDate->format('Y-m-d H:i:s'),
                '$lte' => $endDate->format('Y-m-d H:i:s'),
            ];
        }
        
        
        $result = MongoModel::raw(function ($collection) use ($match) {
            return $collection->aggregate([
                [
                    '$match' => $match,
                ],
                [
                    '$group' => [
                        '_id' => '$seller_id',
                        'Premium' => ['$sum' => '$premium_amount'],
                        'seller_name' => ['$first' => '$seller_name'],
                        'seller_mobile' => ['$first' => '$seller_mobile'],
                        'Policies' => ['$sum' => 1],
                    ],
                ],
                [
                    '$sort' => ['Premium' => -1],
                ],
                [
                    '$limit' => 10,
                ],
                // [
                //     '$limit' => 1
                // ],
            ]);
        });
        if ($result->isEmpty()) {
            return response()->json([
                'success' => false,
                'message' => 'No matching data found',
                'data' => [],
            ], 404);
        }
        $result = $result->map(function ($row, $index) use ($seller_data_id,$seller_data_employee_code) {
            $row['sr_no'] = $index + 1;
            $row['Premium'] = (int) $row['Premium'];

            $employee = (!empty($row['RmCode']) && isset($seller_data_employee_code[$row['RmCode']]))
                        ? $seller_data_employee_code[$row['RmCode']]
                        : ($seller_data_id[$row['_id']] ?? null);

            $seller_name = $employee
                        ? trim(($employee['name'] ?? '') . ' ' . ($employee['middle_name'] ?? '') . ' ' . ($employee['last_name'] ?? ''))
                            . ' (' . ($employee['employee_code'] ?? '') . ')'
                        : 'No Name';
            $seller_mobile = $employee ? $employee['mobile'] : 'N/A';
            $seller_type = $employee ?  getUserTypeIdentifier($employee['usertype']) : 'N/A';
            $row['seller_name'] = $seller_name;
            $row['seller_mobile'] = $seller_mobile;
            $row['seller_type'] = $seller_type;

            return $row;
        });

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Sr.No',
                    'accessorKey' => 'sr_no',
                ],
                [
                    'header' => 'Seller Name',
                    'accessorKey' => 'seller_name',
                ],
                [
                    'header' => 'Seller Mobile',
                    'accessorKey' => 'seller_mobile',
                ],
                [
                    'header' => 'Seller Type',
                    'accessorKey' => 'seller_type',
                ],
                [
                    'header' => 'Policies',
                    'accessorKey' => 'Policies',
                ],
                [
                    'header' => 'Premium Amount',
                    'accessorKey' => 'Premium',
                ],
            ],
            'data' => $result,
        ]);
    }


    public function topRankingDetails(Request $request)
    {

        set_time_limit(0);
        ini_set('memory_limit','-1');
        $role_id = $request->input('roles');
        
        $usertype = $request->usertype;
        
        $startDate = $request->startDate ? Carbon::parse($request->startDate)->startOfDay() : null;
        $endDate = $request->endDate ? Carbon::parse($request->endDate)->endOfDay() : null;

        $lob = $request->lob;

        $user = Auth::user();
        $seller_id = [];
        if ($user->usertype == 1 && $user->is_admin == 'Y') {
            $seller_data_id = User::when(! empty($role_id), function ($q) use ($role_id) {
                    $q->whereHas('userRoles', function ($r) use ($role_id) {
                        $r->where('model_has_roles.role_id', $role_id);
                    });
                })->when(! empty($usertype), function ($q) use ($usertype) {
                        $q->where('usertype', $usertype);
                })
                ->get(['id', 'usertype', 'employee_code','name','middle_name','last_name','mobile'])
                ->mapWithKeys(function ($item) {
                    return [
                        $item->id => [
                            'usertype' => $item->usertype,
                            'employee_code' => $item->employee_code,
                            'name' => credential_decrypt($item->name),
                            'middle_name' => credential_decrypt($item->middle_name),
                            'last_name' => credential_decrypt($item->last_name),
                            'mobile' => credential_decrypt($item->mobile)
                        ]
                    ];
                })
                ->toArray();
            $seller_id = array_keys($seller_data_id);
            $seller_data_employee_code = User::whereIn('usertype',[1,7])->distinct()->get(['usertype', 'employee_code','name','middle_name','last_name','mobile'])
                ->mapWithKeys(function ($item) {
                    return [
                        $item->employee_code => [
                            'usertype' => $item->usertype,
                            'employee_code' => $item->employee_code,
                            'name' => credential_decrypt($item->name),
                            'middle_name' => credential_decrypt($item->middle_name),
                            'last_name' => credential_decrypt($item->last_name),
                            'mobile' => credential_decrypt($item->mobile)
                        ]
                    ];
                })
                ->toArray();
            $seller_employee_code = array_keys($seller_data_employee_code);
        } elseif ($user->usertype == 2 && $user->is_admin == 'Y') {
            $seller_id = User::where('usertype', 2)->pluck('id')->toArray();
        } elseif ($user->usertype == 3 && $user->is_admin == 'Y') {
            $seller_id = User::where('usertype', 3)->pluck('id')->toArray();
        } else {
            if ($user->usertype == 3 && $user->is_admin == 'N') {
                $seller_id = array_column(getUserChildren($user, $user->usertype), 'id');
                $seller_id[] = $user->id;
            } elseif ($user->usertype == 2 && $user->is_admin == 'N') {
                $seller_id = array_column(getUserChildren($user, $user->usertype), 'id');
                $seller_id[] = $user->id;
            } elseif ($user->usertype == 1 && $user->is_admin == 'N') {
                $hierarchyData = getUserLowerHierarchy($user->id, $user->usertype);
                if (! $hierarchyData) {
                    return response()->json([
                        'status' => 500,
                        'message' => 'NO seller data found.',
                    ]);
                }
                $UserIdentifier = getUserTypeFromToken();
                $usersIdWithTypetoFetch = [
                    $UserIdentifier => array_column($hierarchyData, 'id'),
                ];
                $allemployeedata = array_column($hierarchyData, 'employee_code');
                $allemployeedata[] = $user->employee_code;
                $usersIdWithTypetoFetch[$UserIdentifier] = array_merge($usersIdWithTypetoFetch[$UserIdentifier], [$user->id]);

                if ($user->usertype == 1) {
                    $finalMappingData = getMapPosPartner($allemployeedata);
                    $finalpospartnerdata = collect($finalMappingData)
                        ->groupBy('usertype')
                        ->mapWithKeys(function ($group, $key) {
                            return [
                                $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck('id')->all(),
                            ];
                        })
                        ->toArray();
                    if (! empty($finalpospartnerdata)) {
                        $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                    }
                }
                $seller_id = collect($usersIdWithTypetoFetch)->flatten()->toArray();
            }
        }
        $issueStage = $this->transactionStagesQuery();
        $match = [
            'transaction_stage' => ['$in' => $issueStage],
            'seller_name' => ['$nin' => ['', null, 'N/A']],
            '$or' => [
                ['seller_id' => ['$in' => $seller_id]],
                ['RmCode' => ['$in' => $seller_employee_code]]
            ]
        ];

        if (!empty($startDate) && !empty($endDate)) {
            $match['lastupdated_time'] = [
                '$gte' => $startDate->format('Y-m-d H:i:s'),
                '$lte' => $endDate->format('Y-m-d H:i:s'),
            ];
        }

        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $match['section'] = $lob;
        }

        if ($request->has('usertype') && $usertype != '') {
            if ($usertype == 1) {
                $match['RmCode'] = ['$ne' => ''];
            } elseif ($usertype == 7) {
                $match['RmCode'] = ['$eq' => ''];
            } else {
                $match['seller_type'] = getUserTypeIdentifier($usertype);
            }
        }
        
        $result = MongoModel::raw(function ($collection) use ($match) {
            return $collection->aggregate([
                [
                    '$match' => $match,
                ],
                [
                    '$group' => [
                        '_id' => '$seller_id',
                        'Premium' => ['$sum' => '$premium_amount'],
                        'seller_name' => ['$first' => '$seller_name'],
                        'seller_mobile' => ['$first' => '$seller_mobile'],
                        'Policies' => ['$sum' => 1],
                    ],
                ],
                [
                    '$sort' => ['Premium' => -1],
                ],
                [
                    '$limit' => 10,
                ],
                // [
                //     '$limit' => 1
                // ],
            ]);
        });
        if ($result->isEmpty()) {
            return response()->json([
                'success' => false,
                'message' => 'No matching data found',
                'data' => [],
            ], 404);
        }
        $result = $result->map(function ($row, $index) use ($seller_data_id,$seller_data_employee_code) {
            $row['sr_no'] = $index + 1;
            $row['Premium'] = (int) $row['Premium'];

            $employee = (!empty($row['RmCode']) && isset($seller_data_employee_code[$row['RmCode']]))
                        ? $seller_data_employee_code[$row['RmCode']]
                        : ($seller_data_id[$row['_id']] ?? null);

            $seller_name = $employee
                        ? trim(($employee['name'] ?? '') . ' ' . ($employee['middle_name'] ?? '') . ' ' . ($employee['last_name'] ?? ''))
                            . ' (' . ($employee['employee_code'] ?? '') . ')'
                        : 'No Name';
            $seller_mobile = $employee ? $employee['mobile'] : 'N/A';
            $seller_type = $employee ?  getUserTypeIdentifier($employee['usertype']) : 'N/A';
            $row['seller_name'] = $seller_name;
            $row['seller_mobile'] = $seller_mobile;
            $row['seller_type'] = $seller_type;

            return $row;
        });

        return response()->json([
            'status' => 200,
            'column_head' => [
                [
                    'header' => 'Sr.No',
                    'accessorKey' => 'sr_no',
                ],
                [
                    'header' => 'Seller Name',
                    'accessorKey' => 'seller_name',
                ],
                [
                    'header' => 'Seller Mobile',
                    'accessorKey' => 'seller_mobile',
                ],
                [
                    'header' => 'Seller Type',
                    'accessorKey' => 'seller_type',
                ],
                [
                    'header' => 'Policies',
                    'accessorKey' => 'Policies',
                ],
                [
                    'header' => 'Premium Amount',
                    'accessorKey' => 'Premium',
                ],
            ],
            'data' => $result,
        ]);
    }

    public function allTopUsers(Request $request)
    {
        $user = Auth::user();
        $usertypeId = $user->usertype;

        $hierarchyData = getUserChildren($user, $usertypeId);

        if (! $hierarchyData) {
            return response()->json([
                'status' => 500,
                'is_mapping' => false,
                'message' => 'No seller data found.',
            ]);
        }

        $dateFilter = [];
        if ($request->has('start_date') && $request->has('end_date')) {
            $startDate = new \DateTime($request->input('start_date'));
            $endDate = new \DateTime($request->input('end_date'));

            $dateFilter = [
                'lastupdated_time' => [
                    '$gte' => $startDate->format('Y-m-d H:i:s'),
                    '$lt' => $endDate->format('Y-m-d H:i:s'),
                ],
            ];
        }

        $usersIdWithTypetoFetch = [
            $usertypeId => array_column($hierarchyData, 'id'),
        ];

        $allemployeedata = array_column($hierarchyData, 'employee_code');
        $usersIdWithTypetoFetch[$usertypeId] = array_merge($usersIdWithTypetoFetch[$usertypeId], [$user->id]);

        if ($usertypeId == 1) {
            $finalMappingData = getMapPosPartner($allemployeedata);
            $finalpospartnerdata = collect($finalMappingData)
                ->groupBy('usertype')
                ->mapWithKeys(function ($group, $key) {
                    return [
                        ($key == '1') ? 'Employee' : (($key == '2') ? 'POS' : (($key == '3') ? 'Partner' : $key)) => $group->pluck('id')->all(),
                    ];
                })
                ->toArray();

            $usersIdWithTypetoFetchData = [];
            foreach ($usersIdWithTypetoFetch as $key => $value) {
                $mappedKey = ($key === 1) ? 'Employee' : $key;
                $usersIdWithTypetoFetchData[$mappedKey] = $value;
            }

            if (! empty($finalpospartnerdata)) {
                $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetchData, $finalpospartnerdata);
            }
        }

        $issueStage = $this->transactionStagesQuery();
        $finalData = [];

        foreach ($usersIdWithTypetoFetch as $key => $ids) {
            $result = MongoModel::raw(function ($collection) use ($ids, $issueStage, $dateFilter) {

                $match = [
                    'seller_id' => ['$in' => $ids],
                    'transaction_stage' => ['$in' => $issueStage],
                ];

                if (! empty($dateFilter)) {
                    $match = array_merge($match, $dateFilter);
                }

                return $collection->aggregate([
                    [
                        '$match' => $match,
                    ],
                    [
                        '$group' => [
                            '_id' => '$seller_id',
                            'premium_amount' => ['$sum' => '$premium_amount'],
                            'seller_name' => ['$first' => '$seller_name'],
                            'seller_mobile' => ['$first' => '$seller_mobile'],
                            'Policies' => ['$sum' => 1],
                        ],
                    ],
                    [
                        '$sort' => ['premium_amount' => -1],
                    ],
                    [
                        '$limit' => 10,
                    ],
                ]);
            });

            $result = $result->map(function ($row, $index) {
                $row['sr_no'] = $index + 1;

                return $row;
            });

            $finalData[$key] = $result;
        }

        if ($request->has('usertype')) {
            $usertype = $request->input('usertype');

            if (isset($finalData[$usertype])) {
                return response()->json([
                    'status' => 200,
                    'is_mapping' => true,
                    'data' => [
                        $usertype => $finalData[$usertype],
                    ],
                ]);
            } else {

                return response()->json([
                    'status' => false,
                    'is_mapping' => false,
                    'message' => "No Mapping found for $usertype",
                ]);
            }
        } else {

            return response()->json([
                'status' => 200,
                'is_mapping' => true,
                'data' => $finalData,
            ]);
        }
    }

    public function dataFlagCheck(Request $request)
    {
        $user = Auth::user();
        $data_flag = $user->data_flag;
        $is_b2cflag = $user->is_b2cflag;
        if ($is_b2cflag === 1) {
            $sellerTypeAgg = [
                ['seller_type' => ['$in' => ['b2c', 'U']]],
            ];
        }
        if ($user->is_admin == 'N' && ! empty($data_flag)) {
            $sellerTypeAgg[] = [
                'seller_type' => ['$in' => explode(',', $data_flag)],
            ];
        } else {
            $hierarchyConditions = $this->getUserhierarchy($request);

            // Ensure it always returns array of objects
            if (! empty($hierarchyConditions)) {
                foreach ($hierarchyConditions as $condition) {
                    if (is_array($condition)) {
                        $sellerTypeAgg[] = $condition;
                    }
                }
            }
        }

        return $sellerTypeAgg;
    }

    public function Marquee(Request $request)
    {
        $user = Auth::user();
        $Broker = Broker::first()->marquee;
        if ($Broker == 'Y') {
            $Marqueepermission = marquee::where('id', $user->usertype)->pluck('status')->first();
            if ($Marqueepermission && $Marqueepermission[0] == 'Y') {
                $sellerIds = [];
                $isAdmin = false;
                $issueStage = $this->transactionStagesQuery();
                $today = date('Y-m-d');
                $globalMatch = [
                    '$or' => [
                        ['transaction_date' => $today],
                        ['trace_id_created_on' => ['$regex' => "^$today"]],
                    ],
                ];
                if ($user->is_admin == 'Y' && $user->usertype == 1) {
                    $isAdmin = true;
                } elseif ($user->is_admin == 'Y' && $user->usertype == 2) {
                    $sellerIds = User::where('usertype', 2)->plunk('id')->toArray();
                } elseif ($user->is_admin == 'Y' && $user->usertype == 3) {
                    $sellerIds = User::where('usertype', 3)->plunk('id')->toArray();
                } else {
                    $sellerIds = getUserLowerHierarchyWithMapping($user->id, $user->usertype);
                }

                if (! $isAdmin) {
                    $globalMatch['seller_id'] = ['$in' => $sellerIds];
                }

                $result = MongoModel::raw(function ($collection) use ($globalMatch, $today, $issueStage) {
                    return $collection->aggregate([

                        ['$match' => $globalMatch],

                        // then split into facets
                        [
                            '$facet' => [
                                // 1. Total premium + policies issued
                                'total_premium_today' => [
                                    [
                                        '$match' => [
                                            'transaction_date' => $today,
                                            'transaction_stage' => ['$in' => $issueStage],
                                        ],
                                    ],
                                    [
                                        '$group' => [
                                            '_id' => null,
                                            'total_premium' => ['$sum' => '$premium_amount'],
                                            'total_policy_issued' => ['$sum' => 1],
                                        ],
                                    ],
                                ],

                                // 2. Quotes today
                                'quotes_today' => [
                                    [
                                        '$match' => [
                                            'transaction_stage' => 'Quote - Buy Now',
                                            'trace_id_created_on' => ['$regex' => "^$today"],
                                        ],
                                    ],
                                    ['$count' => 'total'],
                                ],

                                // 3. Proposals pending
                                'proposals_pending' => [
                                    [
                                        '$match' => [
                                            'transaction_stage' => 'Proposal Drafted',
                                            'trace_id_created_on' => ['$regex' => "^$today"],
                                        ],
                                    ],
                                    ['$count' => 'total'],
                                ],

                                // 4. Renewals
                                'is_renewal' => [
                                    [
                                        '$match' => [
                                            'is_renewal' => 'Y',
                                        ],
                                    ],
                                    ['$count' => 'total'],
                                ],
                            ],
                        ],
                    ]);
                });
                if ($isAdmin) {
                    $newOnboarded = User::whereDate('created_at', Carbon::today())->count();
                } else {
                    $newOnboarded = User::whereIn('id', $sellerIds)
                        ->whereDate('created_at', Carbon::today())
                        ->count();
                }
                $raw = $result[0] ?? [];

                $final = [
                    'total_premium' => $raw['total_premium_today'][0]['total_premium'] ?? 0,
                    'total_policy_issued' => $raw['total_premium_today'][0]['total_policy_issued'] ?? 0,
                    'quotes_today' => $raw['quotes_today'][0]['total'] ?? 0,
                    'proposals_pending' => $raw['proposals_pending'][0]['total'] ?? 0,
                    'is_renewal' => $raw['is_renewal'][0]['total'] ?? 0,
                    'newOnboarding' => $newOnboarded,
                ];

                return response()->json([
                    'status' => 200,
                    'data' => $final,
                ]);
            } else {
                return response()->json([
                    'status' => 500,
                    'message' => 'No Access For This Usertype.',
                ]);
            }
        } else {
            return response()->json([
                'status' => 500,
                'message' => 'Dont Have Access For This Broker.',
            ]);
        }
    }

    public function businessMetrics(Request $request)
    {

        $stage = StagemasterModel::select('id', 'sub_stage_name')->where('stage_name', 'Issued')->first();
        $subStageList = $stage->sub_stage_name;
        $subStageList = explode(',', $subStageList);
        $SubStages = substagemaster::select('sub_stage_name')->whereIn('id', $subStageList)->get();
        $subStagesArr = $SubStages->pluck('sub_stage_name')->toArray();
        $lobQuery = $this->AllLobs();
        $sections = [];
        $userlist = $this->getUserhierarchy($request);

        foreach ($lobQuery as $key => $value) {
            $sections[] = $value['lob'];
        }
        $mongo2Data = MongoModel::raw(function ($collection) use ($subStagesArr, $sections, $userlist) {
            $sellerTypeAgg = [];
            if (! UserIsAdmin($this->UserId->id)) {
                $sellerTypeAgg[] = [
                    'seller_type' => $this->usertypeIdentifier,
                    'seller_id' => ['$in' => [1, 2, 3, 4]],
                ];
                if (! empty($userlist['PosUsers'])) {
                    $sellerTypeAgg[] = [
                        'seller_type' => 'P',
                        'seller_id' => ['$in' => [1, 2, 3, 4]],
                    ];
                }

            } else {
                $sellerTypeAgg[] = [
                    'seller_type' => ['$in' => [
                        $this->usertypeIdentifier, 'P', 'Partner', 'b2c',
                    ]],
                ];
            }

            return $collection->aggregate([
                [
                    '$match' => [
                        '$or' => $sellerTypeAgg,
                        'section' => ['$in' => $sections],
                        'transaction_stage' => [
                            '$in' => $subStagesArr,
                        ],

                    ],
                ],
                [
                    '$group' => [
                        '_id' => null,  // Group all the results
                        'count' => ['$sum' => 1],
                        'amount' => ['$sum' => '$premium_amount'],
                        'offline_count' => ['$sum' => [
                            '$cond' => [
                                ['$ifNull' => ['$is_offline_entry', false]],
                                1,
                                0,
                            ],
                        ],
                        ],
                        'online_count' => [
                            '$sum' => [
                                '$cond' => [
                                    [
                                        '$or' => [
                                            ['$eq' => ['$is_offline_entry', 1]],  // Count where is_offline_entry is 1
                                            ['$not' => ['$is_offline_entry']],     // Count where is_offline_entry does not exist
                                        ],
                                    ],
                                    1,
                                    0,
                                ],
                            ]],
                        'CARCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'CAR']], 1, 0],
                            ],
                        ],
                        'CarAmount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'CAR']], '$premium_amount', 0],
                            ],
                        ],
                        'PCVCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'PCV']], 1, 0],
                            ],
                        ],
                        'PCVamount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'PCV']], '$premium_amount', 0],
                            ],
                        ],
                        'GCVCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'GCV']], 1, 0],

                            ]],
                        'GCVamount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'GCV']], '$premium_amount', 0],
                            ],
                        ],
                        'HealthCount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'health']], 1, 0],
                            ],
                        ],
                        'HealthAmount' => [
                            '$sum' => [
                                '$cond' => [['$eq' => ['$section', 'health']], '$premium_amount', 0],
                            ],
                        ],
                    ],
                ],
                [
                    '$project' => [
                        'count' => 1,
                        'amount' => 1,
                        'OfflineCount' => '$online_count',
                        'onlineCount' => '$offline_count',
                        'car' => [
                            'count' => '$CARCount',
                            'amount' => '$CarAmount',
                        ],
                        'pcv' => [
                            'count' => '$PCVCount',
                            'amount' => '$PCVamount',
                        ],
                        'gcv' => [
                            'count' => '$GCVCount',
                            'amount' => '$GCVamount',
                        ],
                        'health' => [
                            'count' => '$HealthCount',
                            'amount' => '$HealthAmount',
                        ],
                    ],
                ],
            ]);
        });

        return $mongo2Data;
    }


}
