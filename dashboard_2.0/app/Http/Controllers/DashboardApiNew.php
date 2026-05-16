<?php

namespace App\Http\Controllers;


use App\Models\Broker;
use App\Models\lobMaster;
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
use MongoDB\BSON\UTCDateTime;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Log;
use App\Services\BusinessMetricsService;

class DashboardApiNew extends Controller
{
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

    protected function AllLobs()
    {
        $lobQuery = lobMaster::select('id', 'lob_name', 'lob')->where('is_enabled', 'Y')->get()->toArray();

        return $lobQuery;
    }

    public function businessMetricsDetails(Request $request)
    {

        $startDate = Carbon::createFromFormat('d/m/Y', $request->start_date)->startOfDay();
        $endDate   = Carbon::createFromFormat('d/m/Y', $request->end_date)->endOfDay();
        $lob       = $request->lob ?? 'ALL';


        $sellerTypeAgg = $this->getUserhierarchy($request);

        $stage = StagemasterModel::where('stage_name', 'Issued')->first();

        if (!$stage) {
            return response()->json([
                'success' => false,
                'message' => 'Issued stage not configured'
            ], 422);
        }

        $subStageIds = array_filter(explode(',', $stage->sub_stage_name));

        $subStagesArr = substagemaster::whereIn('id', $subStageIds)
            ->pluck('sub_stage_name')
            ->toArray();

        $metricsService = app(BusinessMetricsService::class);

        $current = $metricsService->premiumCount(
            $startDate,
            $endDate,
            $lob,
            $sellerTypeAgg,
            $subStagesArr
        );

        $prevStart = $startDate->copy()->subMonth();
        $prevEnd   = $endDate->copy()->subMonth();

        $previous = $metricsService->premiumCount(
            $prevStart,
            $prevEnd,
            $lob,
            $sellerTypeAgg,
            $subStagesArr
        );

        if ($previous['policy_count'] == 0) {
            $policyPercentage = $current['policy_count'] == 0 ? 0 : null;
        } else {
            $policyPercentage = (
                ($current['policy_count'] - $previous['policy_count'])
                / $previous['policy_count']
            ) * 100;
        }

        if ($previous['total_premium'] == 0) {
            $premiumPercentage = $current['total_premium'] == 0 ? 0 : null;
        } else {
            $premiumPercentage = (
                ($current['total_premium'] - $previous['total_premium'])
                / $previous['total_premium']
            ) * 100;
        }


        $currentQuoted = $metricsService->policyCountByStage(
            $startDate,
            $endDate,
            'Quote',
            $lob,
            $sellerTypeAgg
        );

        $currentIssued = $metricsService->policyCountByStage(
            $startDate,
            $endDate,
            'Issued',
            $lob,
            $sellerTypeAgg
        );

        $currentConversion = $metricsService->conversionPercentage(
            $currentQuoted,
            $currentIssued
        );

        $stats = [
            [
                'key'   => 'totalPremium',
                'title' => 'Total Premium',
                'value' =>  round($current['total_premium'], 2),
                'delta' =>  round($premiumPercentage, 2),
            ],
            [
                'key'   => 'activeUsers',
                'title' => 'Active Users',
                'value' => '34',
                'delta' => '5%',
            ],
            [
                'key'   => 'monthlyGrowth',
                'title' => 'Monthly Growth',
                'value' =>  round($policyPercentage, 2),
                'delta' =>  round($policyPercentage, 2),
            ],
            [
                'key'   => 'policyIssued',
                'title' => 'Policy Issued',
                'value' => (string) $current['policy_count'],
                'delta' => round($policyPercentage, 2),
            ],
            [
                'key'   => 'conversionRate',
                'title' => 'Conversion Rate',
                'value' => round($currentConversion, 2),
                'delta' => round($currentConversion, 2),
            ],
        ];

        $lobInput  = strtolower($lob);
        $motorLobs = ['car', 'bike', 'cv'];
        $healthLobs = ['health'];
        $insuranceCards = [];

        $insuranceCards = [
            [
                'key'   => 'motor',
                'title' => 'Motor Insurance',
                'metrics' => [
                    [
                        'label' => 'Premium',
                        'value' => round($current['total_premium'], 2),
                        'color' => 'blue',
                    ],
                    [
                        'label' => 'Policies',
                        'value' => (string) $current['policy_count'],
                        'color' => 'red',
                    ],
                    [
                        'label' => 'Quotes',
                        'value' => (string) $currentQuoted,
                        'color' => 'green',
                    ],
                ],
            ],
            [
                'key'   => 'health',
                'title' => 'Health Insurance',
                'metrics' => [
                    [
                        'label' => 'Premium',
                        'value' => round($current['total_premium'], 2),
                        'color' => 'blue',
                    ],
                    [
                        'label' => 'Policies',
                        'value' => (string) $current['policy_count'],
                        'color' => 'red',
                    ],
                    [
                        'label' => 'Quotes',
                        'value' => (string) $currentQuoted,
                        'color' => 'green',
                    ],
                ],
            ],
            [
                'key'   => 'other',
                'title' => 'Other Insurance',
                'metrics' => [
                    [
                        'label' => 'Premium',
                        'value' => round($current['total_premium'], 2),
                        'color' => 'blue',
                    ],
                    [
                        'label' => 'Policies',
                        'value' => (string) $current['policy_count'],
                        'color' => 'red',
                    ],
                    [
                        'label' => 'Quotes',
                        'value' => (string) $currentQuoted,
                        'color' => 'green',
                    ],
                ],
            ],
        ];

        if (in_array($lobInput, $motorLobs)) {
            $insuranceCards[] = [
                'key'   => 'motor',
                'title' => 'Motor Insurance',
                'metrics' => [
                    [
                        'label' => 'Premium',
                        'value' => round($current['total_premium'], 2),
                        'color' => 'blue',
                    ],
                    [
                        'label' => 'Policies',
                        'value' => (string) $current['policy_count'],
                        'color' => 'red',
                    ],
                    [
                        'label' => 'Quotes',
                        'value' => (string) $currentQuoted,
                        'color' => 'green',
                    ],
                ],
            ];
        }

        if (in_array($lobInput, $healthLobs)) {
            $insuranceCards[] = [
                'key'   => 'health',
                'title' => 'Health Insurance',
                'metrics' => [
                    [
                        'label' => 'Premium',
                        'value' => round($current['total_premium'], 2),
                        'color' => 'blue',
                    ],
                    [
                        'label' => 'Policies',
                        'value' => (string) $current['policy_count'],
                        'color' => 'red',
                    ],
                    [
                        'label' => 'Quotes',
                        'value' => (string) $currentQuoted,
                        'color' => 'green',
                    ],
                ],
            ];
        }

        return response()->json([
            'stats' => $stats,
            'insuranceCards' => $insuranceCards
        ], 200);
    }



    public function businessOperationDetails(Request $request)
    {
        $lob = $request->input('lob');
        $sections = [];

        $sellerTypeAgg = $this->dataFlagCheck($request);

        if ($request->has('lob') && $lob != 'All' && $lob != '') {
            $sections = [$lob];
        } else {
            $lobQuery = $this->AllLobs();
            foreach ($lobQuery as $value) {
                $sections[] = $value['lob'];
            }
        }


        $stage = StagemasterModel::where('stage_name', 'Issued')->first();

        if (!$stage) {
            return response()->json([
                'status' => 422,
                'message' => 'Issued stage not configured'
            ]);
        }

        $subStageIds = array_filter(explode(',', $stage->sub_stage_name));

        $subStagesArr = substagemaster::whereIn('id', $subStageIds)
            ->pluck('sub_stage_name')
            ->toArray();



        $andConditions = [
            ['section' => ['$in' => $sections]],
            ['transaction_stage' => ['$in' => $subStagesArr]],
            ['$or' => $sellerTypeAgg],
        ];

        if (Auth::user()->usertype == 4) {

            $utmParameter = activeRoleCodeMappingUser();

            if (!empty($utmParameter)) {

                $utmOrConditions = [];

                foreach ($utmParameter as $key => $value) {

                    if ($key == 'utm_medium') {
                        $key = 'utm_media';
                    }

                    $brokerKey = 'broker_' . $key;
                    $valueArr = explode(',', $value);

                    $utmOrConditions[] = count($valueArr) > 1
                        ? [$brokerKey => ['$in' => $valueArr]]
                        : [$brokerKey => $value];
                }

                $andConditions[] = ['$or' => $utmOrConditions];
            }
        }

        $matchStage = [
            '$match' => [
                '$and' => $andConditions
            ]
        ];

        if ($request->has('startDate') && $request->has('endDate')) {


            $startDate = Carbon::createFromFormat('d/m/Y', $request->startDate)->startOfDay();
            $endDate   = Carbon::createFromFormat('d/m/Y', $request->endDate)->endOfDay();

            $matchStage['$match']['lastupdated_time'] = [
                
                '$gte' => $startDate->format('Y-m-d') . ' 00:00:00',
                '$lte' => $endDate->format('Y-m-d') . ' 23:59:59',
                
            ];
        }

        if ($request->has('empIds')) {

            $empIds = $request->input('empIds');

            if (!empty($empIds)) {

                if (!is_array($empIds)) {
                    $empIds = [$empIds];
                }

                $matchStage['$match']['seller_id'] = ['$in' => $empIds];
            }
        }

        $sortStage = [
            '$sort' => ['lastupdated_time' => -1]
        ];

        $limitStage = [
            '$limit' => 5
        ];

        $projectStage = [
            '$project' => [
                'proposer_name' => 1,
                'section' => 1,
                'premium_amount' => 1,
                'lastupdated_time' => 1,
                '_id' => 0
            ]
        ];

        $query = [
            $matchStage,
            $sortStage,
            $limitStage,
            $projectStage
        ];

        $results = MongoModel::raw(function ($collection) use ($query) {
            return $collection->aggregate($query);
        });

        $recentPolicies = [];
        $index = 1;

        foreach ($results as $policy) {

            $daysAgo = \Carbon\Carbon::parse($policy['lastupdated_time'])
                ->diffForHumans();

            $recentPolicies[] = [
                'id' => $index++,
                'name' => $policy['proposer_name'] ?? 'N/A',
                'subText' => $policy['section'] ?? 'N/A',
                'value' => (string) ($policy['premium_amount'] ?? 0),
                'meta' => ucfirst($daysAgo),
            ];
        }

        return response()->json([
            'status' => 200,
            'recentPolicies' => $recentPolicies,
            'message' => 'Records Found'
        ]);
    }
}
