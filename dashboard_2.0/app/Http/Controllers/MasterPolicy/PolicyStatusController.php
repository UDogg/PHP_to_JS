<?php

namespace App\Http\Controllers\MasterPolicy;

use App\Exports\AllDataExport;
use App\Jobs\ExportLargeExcel;
use App\Jobs\fetchExcelData;
use App\Models\ExcelDownloadLog;
use App\Models\MongoModel;
use Illuminate\Http\Request;
use Illuminate\Http\Response;
use App\Models\substagemaster;
use Illuminate\Pagination\LengthAwarePaginator;
use Illuminate\Support\Carbon;
use App\Models\StagemasterModel;
use App\Http\Requests\EnableCols;
use Illuminate\Support\Facades\DB;
use app\Services\MotorFetchService;
use App\Services\PolicyStatusCountService;
use App\Interfaces\PolicyStatusData;
use App\Http\Requests\UpdtColumnMaster;
use App\Models\lobMaster as lob_master;
use App\Models\PolicyStatusColumnMaster;
use App\Http\Controllers\DataExportController;
use App\Models\CtaMasterModel;
use App\Models\MisReportConfigurator;
use App\Models\User;
use Illuminate\Support\Facades\Auth;
use App\Models\policy_status_column_relation_master;
use App\Models\PolicyStatusFilterMaster;
use App\Models\userTypes;
use Illuminate\Pagination\Paginator;
use Illuminate\Support\Facades\Storage;
use Illuminate\Support\Str;
use Maatwebsite\Excel\Facades\Excel;
use MongoDB\BSON\Regex;
use App\Http\Controllers\MasterPolicy\DateTime;
use Illuminate\Support\Facades\Log;
use Illuminate\Support\Facades\Http;
class PolicyStatusController
{

    public function __construct(public PolicyStatusData $section)
    {
    }

    /**
     * Build MongoDB query with complex $and and $or operators
     * Uses dynamic values from stages function logic
     * 
     * @param array $sections - Array of sections to filter (from stages function)
     * @param string $startDate - Start date in format 'Y-m-d H:i:s' (from stages function)
     * @param string $endDate - End date in format 'Y-m-d H:i:s' (from stages function)
     * @param array $transactionStages - Array of transaction stages (from stages function)
     * @param array $usersIdWithTypetoFetch - User hierarchy data with seller types and IDs
     * @param object $user - User object to get employee_code (RmCode)
     * @param bool $b2c_flag - B2C flag to include b2c and U seller types
     * @return array - MongoDB query array
     */
    private function buildMongoQuery(
        array $sections,
        string $startDate,
        string $endDate,
        array $transactionStages,
        array $usersIdWithTypetoFetch,
        $user,
        bool $b2c_flag = false
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
            
            if ($canUseRmCode && in_array($sellerType, ['E', 'SP'])) {
                $typeConditions[] = [
                    'RmCode' => $rmCode
                ];
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
                ],
                [
                    'transaction_stage' => [
                        '$in' => $transactionStages
                    ]
                ]
            ]
        ];
        
        if (!empty($sellerOrConditions)) {
            $query['$and'][] = [
                '$or' => $sellerOrConditions
            ];
        }
        
        return $query;
    }

    public function index(Request $request)
    {
        $isRenewal = stripos(\Illuminate\Support\Facades\URL::current(), 'policystatus_renewal') !== false;


        $motorFetchData = $this->section->fetchdata($isRenewal);
        $data = $motorFetchData[0] ?? "" ;
        $stagecount = $motorFetchData[1] ?? "";
        $listCounts = $motorFetchData[2] ?? "";
        $perPage = $motorFetchData[3]  ?? "";
        $stageFilter = $motorFetchData[4] ?? "";
        $PolicyStatusColumnMasterArray = $motorFetchData[5] ?? "";
        $col_arr = $motorFetchData[6] ?? "";
        $paginationCount =  $motorFetchData[7] ?? "";


        if (!empty($motorFetchData)) {
            return view('policy_status.policystatus', compact('data', 'stagecount', 'listCounts', 'perPage', 'stageFilter', 'PolicyStatusColumnMasterArray', 'col_arr', 'paginationCount'));
          
        } else {
            return response()->json([
                'status' => "500",
                'message' => "\nSomething went wrong. Please try again later.",

            ],500);
        }

    }

    public function stages(Request $request)
    {
        $user = Auth::user();

        $listingPermission = "Policy Status.view";
        if (!$user->can($listingPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $perPage = $request->perpage ?? 10;
        $pageNo = ($request->pageNo - 1) ?? 0;
        $offsetVal = $pageNo * $perPage;
        $offset = $request->input('offset', $offsetVal);
        $limit = $request->input('limit', $perPage);
        $isRenewal = $request->is_renewal == 'Y' ? true : false;
        $filter_value = $request[ 'filter_value' ] ?? [];
        if (!is_array($filter_value)) {
            $filter_value = [];
        }
        $excelExport = !empty($request[ 'excelExport' ]) ? true : false;

        //fetch data using user_id and user_type
        $user = Auth::user();
        $b2c_flag = $user->is_b2cflag;
        $data_flag = $user->data_flag;
        $UserIdentifier = getUserTypeFromToken();
        $userType = $user->usertype;
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
            $userType = $user->usertype;
            $userId = $user->id;
            $isAdmin = $user->is_admin;
        }


        if ($userType == 4) {
            $usersIdWithTypetoFetch = [
                'b2c' => [],
                'U' => []
            ];
        }elseif($isAdmin == "Y"){
            switch ($userType) {
                case '1':                    
                    if(config('fetch_sp_details')){
                        $usersIdWithTypetoFetch = [
                            'E' => [],
                            'P' => [],
                            'Partner' => [],
                            'SP' => [],
                        ];
                    }else{
                        $usersIdWithTypetoFetch = [
                            'E' => [],
                            'P' => [],
                            'Partner' => [],
                        ];
                    }
                    break;
                case '2':
                    $usersIdWithTypetoFetch = [
                    'P' => []
                ];
                    break;
                case '3':
                    $usersIdWithTypetoFetch = [
                    'Partner' => []
                ];
                    break;
                case '4':
                    $usersIdWithTypetoFetch = [
                    'b2c' => [],
                    'U' => []
                ];
                case '7':
                    $usersIdWithTypetoFetch = [
                    'SP' => [],
                ];
                    break;
                default:
                    return response()->json([
                        'status' => 500,
                        'message' => 'Invalid user type'
                    ], 500);
                    
            }
        }else {
            $hierarchyData = getUserLowerHierarchy($userId, $userType);
            if (empty($hierarchyData)) {
                $usersIdWithTypetoFetch[$UserIdentifier] = [$user->{$dataFetchFrom}];
                $getUserEmpCode = $user->employee_code;

                if($userType == 1){
                    $sp_exists = userTypes::where('Identifier', 'SP')->exists();
                    if($sp_exists){
                        $usersIdWithTypetoFetch['SP'] = [$user->{$dataFetchFrom}];
                    }
                    $finalMappingData = getMapPosPartner([$getUserEmpCode]);
                                            $finalpospartnerdata = collect($finalMappingData)
                                                ->groupBy('usertype')
                                                ->mapWithKeys(function ($group, $key) use ($dataFetchFrom) {
                                                    return [
                                                        $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck($dataFetchFrom)->all()
                                                    ];
                                                })
                                                ->toArray();
                    if(!empty($finalpospartnerdata)){
                        $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                    }
                } 
            }else {
                $usersIdWithTypetoFetch = [
                        $UserIdentifier => array_column($hierarchyData, $dataFetchFrom)
                    ];
                    $allemployeedata = array_column($hierarchyData, 'employee_code');
                    $allemployeedata[] = $user->employee_code;
                    $usersIdWithTypetoFetch[$UserIdentifier] = array_merge($usersIdWithTypetoFetch[ $UserIdentifier], [$userId]);

                    
                if($userType == 1){
                    $sp_exists = userTypes::where('Identifier', 'SP')->exists();
                    if($sp_exists){
                        $usersIdWithTypetoFetch['SP'] = [$user->{$dataFetchFrom}];
                    }
                    $finalMappingData = getMapPosPartner($allemployeedata);
                                            $finalpospartnerdata = collect($finalMappingData)
                                                ->groupBy('usertype')
                                                ->mapWithKeys(function ($group, $key) use ($dataFetchFrom) {
                                                    return [
                                                        $key == '2' ? 'P' : ($key == '3' ? 'Partner' : $key) => $group->pluck($dataFetchFrom)->all()
                                                    ];
                                                })
                                                ->toArray();
                    if(!empty($finalpospartnerdata)){
                        $usersIdWithTypetoFetch = array_merge($usersIdWithTypetoFetch, $finalpospartnerdata);
                    }
                }   

            }
        }

        // end logic for user hierarchy
        $section = [];
        $stagecount = [];
        $data = '';
        $listCounts = 0;
        if ($request->has('filter_value') && $request->has('filter_value') != "" && $request->has('filter_value.LOB')) {
            if(is_array($request[ 'filter_value' ][ 'LOB' ])){
                $section = array_merge($section, $request[ 'filter_value' ][ 'LOB' ]);
            }else{
                if(in_array(strtolower($request[ 'filter_value' ][ 'LOB' ]),['health','top_up','term','travel','pet'])){
                    $section[] = strtolower($request[ 'filter_value' ][ 'LOB' ]);
                }else{
                    $section[] = strtoupper($request[ 'filter_value' ][ 'LOB' ]);
                }
            }
            // array_push($section,  $request['lobFilter']);
        } else {
            $lobValue = lob_master::where('is_enabled', 'Y')->get();
            foreach ($lobValue as $value) {
                $is_enabled = $value[ 'is_enabled' ];
                if ($is_enabled == "Y") {
                    array_push($section, $value[ 'lob' ]);
                }
            }
        }

        if (!$excelExport) {

            $policyStatusCountService = new PolicyStatusCountService();
            $stagecount = $policyStatusCountService->getPolicyStatusCounts($request,$user, $filter_value, $usersIdWithTypetoFetch, $b2c_flag, $data_flag, $section);
        }
       
        $lobFilter = [];
        $query = lob_master::query();
        if (config('lob_order_by') == 1) {
            $query->orderBy('lob_order_by', 'ASC');
        }
        $lobValue = $query->get();

        foreach ($lobValue as $value) {
            $is_enabled = $value[ 'is_enabled' ];
            if ($is_enabled == "Y") {
                array_push($lobFilter, $value[ 'lob' ]);
            }
        }
        $motorFetchService = new MotorFetchService();
        $stageFilterarray = $motorFetchService->stageFilter();
        $stageFilter = $stageFilterarray[ 0 ];


        $columnName = [];
         $startDate = "";
        $endDate = "";
        $lobFilter = $request[ 'lobFilter' ] ?? "";
        $searchValue = $request[ 'searchValue' ] ?? '';
      
        //  \DB::connection('mongodb')->enableQueryLog();

        // $listCounts = MongoModel::select('trace_id');
        $tempValue = [];
        $templateId = $request[ 'template_id' ] ?? '';
        $transactionStage = $request[ 'transaction_stage' ] ?? '';
        // $requestAllData = $request->all();
        // $tempdatastore = [];

        $MisColumnName = [];


        // foreach ($requestAllData as $head => $value) {
        //     $results = DB::table('policy_status_filter_master as f')
        //         ->join('policystatus_column_master as c', 'f.column', '=', 'c.id')
        //         ->select('f.filtername', 'f.key', 'f.value', 'f.column', 'c.column_name')
        //         ->where('f.value', $value)
        //         ->get();
        //     foreach ($results as $result) {
        //         $columnNameKey = $result->column_name;
        //         $columnNameValue = $result->key;
        //         // Using a unique key in the associative array to ensure uniqueness
        //         $uniqueKey = $columnNameKey . '=' . $columnNameValue;
        //         $tempdatastore[$uniqueKey] = [$columnNameKey, '=', $columnNameValue];
        //     }
        // }

        // $tempdatastore = array_values($tempdatastore);
        $dataQuery = MongoModel::whereIn('section', $section)->orderBy('lastupdated_time', 'desc');

        if (!empty($filter_value['Report Type']) && is_array($filter_value['Report Type'])) {

            $startDate = Carbon::createFromFormat('d/m/Y', trim($request['startDate']));
            $endDate   = Carbon::createFromFormat('d/m/Y', trim($request['endDate']));

            $reportDateColumn = $filter_value['Report Type'][0];

            $dataQuery->whereBetween($reportDateColumn, [ $startDate->format('Y-m-d') . " 00:00:00",
                  $endDate->format('Y-m-d') . " 23:59:59"]);

        }
        if (!empty($filter_value)) {
            foreach ($filter_value as $key => $value) {
               
                if ($key === 'Report Type') {
                    continue;
                }
                $results = PolicyStatusFilterMaster::join('policystatus_column_master as b', 'policy_status_filter_master.column', '=', 'b.id')
                    ->select(
                        'policy_status_filter_master.filtername',
                        'policy_status_filter_master.key',
                        'policy_status_filter_master.value',
                        'policy_status_filter_master.lob',
                        'b.column_name',
                        'b.id'
                    )
                    ->where('policy_status_filter_master.filtername', $key)
                    ->where('policy_status_filter_master.value', $value)
                    ->first();

                if ($results) {
                    $dataQuery = $dataQuery->whereIn(($results->column_name ?? ''), (explode(',', $results->value) ?? ''));
                }
            }
        }


        if ($user->usertype == 4) {
            $utmParameter = activeRoleCodeMappingUser();

            if (!empty($utmParameter)) {
                $dataQuery = $dataQuery->where(function ($query) use ($utmParameter) {

                    $query->where(function ($orQuery) use ($utmParameter) {

                        if (isset($utmParameter['utm_campaign'])) {
                            $orQuery->orWhereIn('broker_utm_campaign', explode(',', $utmParameter['utm_campaign']));
                        }
        
                        if (isset($utmParameter['utm_source'])) {
                            $orQuery->orWhereIn('broker_utm_source', explode(',', $utmParameter['utm_source']));
                        }
        
                    });

                });
            }

        }
        if (!empty($request[ 'startDate' ]) && !empty($request[ 'endDate' ])) {
            $startDate = $request['startDate'];
            $endDate   = $request['endDate'];
            if (!empty($request->filter_value['Date range'])) {
                $daterange = $request->filter_value['Date range'];
                [$startDate, $endDate] = explode('-', $daterange);
            }
            $startDate = Carbon::createFromFormat('d/m/Y', trim($startDate));
            $endDate   = Carbon::createFromFormat('d/m/Y', trim($endDate)); 

            if ($isRenewal) {
                $dataQuery = $dataQuery->whereBetween('policy_end_date', [
                    $startDate->format('Y-m-d'),
                    $endDate->format('Y-m-d')
                ]);
            } elseif(empty($filter_value['Report Type'])) {
                $dataQuery = $dataQuery->whereBetween('lastupdated_time', [
                    $startDate->format('Y-m-d') . " 00:00:00",
                    $endDate->format('Y-m-d') . " 23:59:59"
                ]);
            }
        }
        
        $renewalFilter = substagemaster::select('sub_stage_name')->where('is_renewal', 'Y')->get();
        $renewalFilters = $renewalFilter->pluck('sub_stage_name')->toArray();

        if (!empty($templateId)) {
            $MisReportStage = MisReportConfigurator::select('stage_name')->where('mis_report_configurator_id', $templateId)->first();
            $templateIdStage = $MisReportStage->stage_name ?? '';
            $templateIdStage = json_decode($templateIdStage, true);

            $stagesArray = StageToSubStage($templateIdStage);
            $dataQuery = $dataQuery->whereIn('transaction_stage', $stagesArray);

            if (!empty($request->filter_value['LOB']) && is_array($request->filter_value['LOB'])) {
                $lobValues = $request->filter_value['LOB'];
                $lobFilter = ['section' => ['$in' => $lobValues]];
                $dataQuery = $dataQuery->where($lobFilter);
            } elseif (!empty($request->filter_value['LOB'])) {
                $lobValue = $request->filter_value['LOB'];
                $lobFilter = [
                    'section' => is_array($lobValue) ? ['$in' => $lobValue] : $lobValue
                ];
                $dataQuery = $dataQuery->where($lobFilter);
            }

        } elseif ($isRenewal) {
            $dataQuery = $dataQuery->whereIn('transaction_stage', $renewalFilters);
        } elseif (!empty($transactionStage)) {

            $sub_stage_name = [];
            $sub_stage_name = StageToSubStage($transactionStage);
            $dataQuery = $dataQuery->whereIn('transaction_stage', $sub_stage_name);
        } else {
            $defaultStage = StagemasterModel::orderBy('priority')->first()->stage_name;
            $sub_stage_name = StageToSubStage($defaultStage);
            $dataQuery = $dataQuery->whereIn('transaction_stage', $sub_stage_name);
        }
        
        $transactionStagesForQuery = [];
        if (!empty($templateId)) {
            $transactionStagesForQuery = $stagesArray ?? [];
        } elseif ($isRenewal) {
            $transactionStagesForQuery = $renewalFilters;
        } elseif (!empty($transactionStage)) {
            $transactionStagesForQuery = $sub_stage_name ?? [];
        } else {
            $transactionStagesForQuery = $sub_stage_name ?? [];
        }
        
        $queryStartDate = '';
        $queryEndDate = '';
        if (!empty($request['startDate']) && !empty($request['endDate']) && !$isRenewal && empty($filter_value['Report Type'])) {
            if (isset($startDate) && $startDate instanceof Carbon) {
                $queryStartDate = $startDate->format('Y-m-d') . " 00:00:00";
                $queryEndDate = $endDate->format('Y-m-d') . " 23:59:59";
            }
        } elseif (!empty($filter_value['Report Type']) && is_array($filter_value['Report Type'])) {
            if (isset($startDate) && $startDate instanceof Carbon) {
                $queryStartDate = $startDate->format('Y-m-d') . " 00:00:00";
                $queryEndDate = $endDate->format('Y-m-d') . " 23:59:59";
            }
        }
        
        $useMongoQuery = false;
        if (!empty($queryStartDate) && !empty($queryEndDate) && !empty($transactionStagesForQuery) && !empty($section)) {
            $mongoQuery = $this->buildMongoQuery(
                sections: $section,
                startDate: $queryStartDate,
                endDate: $queryEndDate,
                transactionStages: $transactionStagesForQuery,
                usersIdWithTypetoFetch: $usersIdWithTypetoFetch,
                user: $user,
                b2c_flag: $b2c_flag
            );
            
            $dataQuery = MongoModel::where($mongoQuery)->orderBy('lastupdated_time', 'desc');
            $useMongoQuery = true;
        }

        if (!empty($searchValue)) {
            $dataQuery = $dataQuery->where(function ($query) use ($searchValue) {
                $query->where('trace_id', 'regex', '/' . $searchValue . '/i')
                    ->orWhere('proposer_mobile', 'regex', '/' . $searchValue . '/i')
                    ->orWhere('vehicle_registration_number', 'regex', '/' . $searchValue . '/i')
                    ->orWhere('proposer_name', 'regex', '/' . $searchValue . '/i')
                    ->orWhere('proposer_emailid', 'regex', '/' . $searchValue . '/i')
                    ->orWhere('policy_no', 'regex', '/' . $searchValue . '/i');
            });
        }


        if (!empty($filter_value)) {
            $stageMasterModel = StagemasterModel::where('stage_name', $filter_value)->first();
        } else {
            $stageMasterModel = StagemasterModel::select('stage_name', 'priority', 'sub_stage_name', 'id')->first();
        }
        $substageValue = $stageMasterModel->sub_stage_name ?? '';
        $substage = substagemaster::select('id', 'sub_stage_name')->whereIn('id', explode(",", $substageValue))->get();
        foreach ($substage as $stageVal) {
            $tempValue[] = $stageVal[ 'sub_stage_name' ];
        }
        $substage = $tempValue ?? '';
        // if (!empty($substage)) {
        //     $listCounts = $listCounts->whereIn('transaction_stage', $substage);
        // } else {
        //     $listCounts = $listCounts->whereIn('section', $section);
        // }
       
        $keyExist = array_intersect($renewalFilters, $substage);
        // if ($isRenewal) {
        //     $listCounts = $listCounts->whereIn('transaction_stage', $keyExist);
        // }

        // $stageNameData = $stageMasterModel[ 'id' ] ?? '';
        // $MisColumnAlias = [];
        $columnData = self::columnData($request);

        //column wise filter code start
        $defaultColumns = $columnData[ 'data' ][ 'default_column' ];

        if ($request->has('keys')) {
            $mappedArray = [];
            $keys = $request->keys;

            foreach ($keys as $key => $value) {
                foreach ($defaultColumns as $column) {
                    // Normalize by trimming or removing trailing dot to match properly
                    if ($column[ 'alias' ] != null) {
                        if (rtrim($column[ 'alias' ], '.') == $key) {
                            $mappedArray[$column[ 'column_name' ]] = $value;
                            break;
                        }
                    } else {
                        if (rtrim($column[ 'column_name' ], '.') == $key) {
                            $mappedArray[$column[ 'column_name' ]] = $value;
                            break;
                        }
                    }
                }
            }
            if (!empty($mappedArray)) {
                $dataQuery = $dataQuery->where(function ($query) use ($mappedArray) {
                    foreach ($mappedArray as $column => $value) {
                        $query->Where($column, 'regex', '/' . $value . '/i');
                    }
                });

            }
        }
        //column wise filter code end

        if (!empty($transactionStage)) {
            $stageMasterModelData = StagemasterModel::select('id', 'stage_name')->where('stage_name', $transactionStage)->first();
        } else {
            $stageMasterModelData = StagemasterModel::select('id', 'stage_name')->orderBy('priority')->limit(1)->first();
        }
        $stageMasterModelData = CtaMasterModel::select('cta_name')->where('stage', $stageMasterModelData[ 'id' ])->first();
        if (!empty($stageMasterModelData)) {
            $redirectionUrl = $stageMasterModelData[ 'cta_name' ];
            array_push($columnName, $redirectionUrl);
        }


        foreach (($columnData[ 'data' ] ?? []) as $key => $value) {
            foreach ($value as $key => $value) {
                $columnName[] = $value[ 'column_name' ];
            }
        }
        if (!empty($templateId)) {
            $MisReportColumn = MisReportConfigurator::select('columns')->where('mis_report_configurator_id', $templateId)->orderBy('sequence')->first();
            if (!empty($MisReportColumn)) {
                $MisReportColumn = json_decode($MisReportColumn->columns, true);
                // dump($MisReportColumn);
                // $MisAliasColumnData = PolicyStatusColumnMaster::select('column_name', 'alias')->get()->toArray();
                // dump($MisAliasColumnData);
                foreach ($MisReportColumn as $key => $value) {
                    $MisColumnName[] = $value;
                    // foreach ($MisAliasColumnData as $key => $misvalue) {
                    //     if($misvalue['column_name'] == $value)
                    //     {
                    //         $MisColumnAlias[$misvalue['column_name']] =  $misvalue['alias'];
                    //     }
                    // }

                }

                $dataQuery = $dataQuery->select($MisColumnName);
            } else {
                return ([
                    'status' => 500,
                    'message' => 'No Data Found'
                ]);
            }
        } else {
            if ($transactionStage == 'Inspection') {
                $columnName[] = 'transaction_stage';
            }
            $dataQuery = $dataQuery->select($columnName);
        }

      
        $sellerId = !empty($sellerId) ? (array) $sellerId : [];
        $sellerTypeUnique = !empty($sellerTypeUnique) ? (array) $sellerTypeUnique : [];

        // Skip user hierarchy filtering if buildMongoQuery was used (it already includes this logic)
        if (!$useMongoQuery) {
            $dataQuery = $dataQuery->where(function ($query) use ($sellerId, $sellerTypeUnique, $b2c_flag, $data_flag, $usersIdWithTypetoFetch,$user) {

                if ($b2c_flag) {
                    $query->orWhereIn('seller_type', ['b2c', 'U']);
                }

                if (empty($data_flag)) {
                    // if (!empty($sellerId) || !empty($sellerTypeUnique)) {
                    // $query->orWhere(function ($subQuery) use ($sellerId, $sellerTypeUnique) {
                    //     if (!empty($sellerId)) {
                    //         $subQuery->whereIn('seller_id', $sellerId);
                    //     }
                    //     if (!empty($sellerTypeUnique)) {
                    //         $subQuery->whereIn('seller_type', $sellerTypeUnique);
                    //     }
                    // });
                    $query->orWhere(function ($sub) use ($usersIdWithTypetoFetch, $user) {
                        foreach ($usersIdWithTypetoFetch as $type => $ids) {
                            $sub->orWhere(function ($q) use ($type, $ids, $user) {
                                $q->where('seller_type', $type)
                                  ->where(function ($inner) use ($ids, $user) {
                                      if (!empty($ids)) {
                                          $inner->whereIn('seller_id', $ids);
                                      }
                                      if ($user->usertype == 1) {
                                          $inner->orWhere('RmCode',$user->employee_code);
                                      }
                                  });
                            });
                        }
                    });
                    
                    // }
                } else {
                    $query->orWhere(function ($subQuery) use ($data_flag, $user) {
                        $subQuery->whereIn('seller_type', explode(',', $data_flag));
                        $subQuery->Where('RmCode', $user->employee_code);
                    });
                }
            });
        }
        // $paginationCount = $dataQuery->count();


        $hasSellerFilter = false;
$sellerIds = [];

foreach ($usersIdWithTypetoFetch as $type => $ids) {
    if (!empty($ids) && is_array($ids)) {
        $sellerIds = array_merge($sellerIds, $ids);
        $hasSellerFilter = true;
    }
}

$sellerIds = array_values(array_unique($sellerIds));

$paginationCount = 0;
if ($hasSellerFilter) {
    $paginationCount = (clone $dataQuery)
        // ->whereIn('seller_id', $sellerIds)
        ->count();
} else {
    $paginationCount = $dataQuery->count();
}

//         $paginationCount = 0;

// // collect all seller ids safely
// $sellerIds = [];
// foreach ($usersIdWithTypetoFetch as $type => $ids) {
//     if (!empty($ids) && is_array($ids)) {
//         $sellerIds = array_merge($sellerIds, $ids);
//     }
// }
// $sellerIds = array_values(array_unique($sellerIds));

// $chunks = array_chunk($sellerIds, 500);

// foreach ($chunks as $chunk) {

//     $clone = clone $dataQuery;

//     $clone->where(function ($q) use ($chunk) {
//         $q->whereIn('seller_id', $chunk);
//     });

//     $paginationCount += $clone->count();
// }

        // dd($dataQuery);
        
        $col_name = [];
        if (!$excelExport) {
            
            // $data = $dataQuery->offset($offset)->limit($limit)->get();

             if ($hasSellerFilter) {
        $data = (clone $dataQuery)
            // ->whereIn('seller_id', $sellerIds)
            ->offset($offset)
            ->limit($limit)
            ->get();
    } else {
        $data = $dataQuery
            ->offset($offset)
            ->limit($limit)
            ->get();
    }
//             $data = collect();

// foreach ($chunks as $chunk) {

//     $clone = clone $dataQuery;

//     $clone->where(function ($q) use ($chunk) {
//         $q->whereIn('seller_id', $chunk);
//     });

//     $data = $data->merge(
//         $clone->limit($limit)->get()
//     );

//     if ($data->count() >= $limit) {
//         break;
//     }
// }

// $data = $data->slice(0, $limit)->values();
            // dd(\DB::connection('mongodb')->getQueryLog(),$data);
            // Log::info(\DB::connection('mongodb')->getQueryLog(),$data);

// dd($data);
            if (in_array('reporting_employee', $columnName)) {
                $mobiles = $data->pluck('seller_mobile')->filter()->unique()->map(function ($mobile) {
                    return credential_encrypt($mobile);
                });

                $sellerUsers = User::whereIn('mobile', $mobiles)->get()->keyBy('mobile');

                $reportingToIds = $sellerUsers->pluck('reportingto')->filter()->unique();
                $employeeCodes = $sellerUsers->pluck('employee_code')->filter()->unique();

                $reportingUsers = User::whereIn('id', $reportingToIds)
                    ->orWhere(function ($q) use ($employeeCodes) {
                        $q->whereIn('employee_code', $employeeCodes)
                            ->where('usertype', 1);
                    })->get();

                $reportingById = $reportingUsers->keyBy('id');
                $reportingByCode = $reportingUsers->where('usertype', 1)->keyBy('employee_code');
            }

            $pdf_access = config('shared_pdf');
            $pdf_access = !empty($pdf_access)? explode(',', $pdf_access):[];
            foreach ($data as $key => $value) {
                if (!empty($pdf_access) && in_array($value->seller_type, $pdf_access)) {
                        $value->share_pdf = true;
                }else{
                    $value->share_pdf = false;
                }

                if (isset($value->proposal_url)) {
                    $value->common_redirect_url = $value->proposal_url;
                    unset($value->proposal_url);
                }
                if (isset($value->quote_url)) {
                    $value->common_redirect_url = $value->quote_url;
                    unset($value->quote_url);
                }
                if (!empty($value->policy_doc_path) && config('s3_download_link') == true) {
                    $parsedUrl = parse_url($value->policy_doc_path);

                    if (!empty($parsedUrl[ 'path' ])) {
                        $fileKey = ltrim($parsedUrl[ 'path' ], '/');

                        $value->policy_doc_path = Storage::disk('s3')->temporaryUrl(
                            $fileKey,
                            now()->addDays(7)
                        );
                    }
                }
                if (in_array('reporting_employee', $columnName)) {
                    $encryptedMobile = credential_encrypt($value->seller_mobile);
                    $sellerUser = $sellerUsers[$encryptedMobile] ?? null;

                    if ($sellerUser) {
                        if ($value->seller_type === 'E') {
                            $reportingUser = $reportingById[$sellerUser->reportingto] ?? null;
                        } else {
                            $reportingUser = $reportingByCode[$sellerUser->employee_code] ?? null;
                        }

                        $value->reporting_employee = $reportingUser
                            ? credential_decrypt($reportingUser->name) . ' ' . credential_decrypt($reportingUser->last_name)
                            : null;
                    } else {
                        $value->reporting_employee = null;
                    }
                }
                if ($transactionStage == 'Inspection') {

                    if ($value->transaction_stage == 'Inspection Pending') {
                        if(config('Fetch_Inspection_status_by_API')){
                            $value->common_redirect_url = true;
                            $value->inspection_api = true;
                        }else{
                            $value->common_redirect_url = config('Inspection_check_api');
                            $value->inspection_api = false;
                        }
                        unset($value->transaction_stage);

                    } else {
                        $value->common_redirect_url = $value->proposal_url;
                        unset($value->transaction_stage);
                    }
                }

                if (config('PunchedPartnerPoliciesToEmployee') == true) {

                    if ($value->seller_type == 'Partner') {
                        $encryptedMobile = credential_encrypt($value->seller_mobile);
                        $sellerUser = User::whereIn('mobile', [$encryptedMobile])->first();

                        // $sellerUser = $sellerUsers[$encryptedMobile] ?? null; 
                        if ($sellerUser) {

                            if ($value->seller_type === 'E') {
                                $reportingUser = $reportingById[$sellerUser->reportingto] ?? null;
                            } else {
                                $reportingUser = User::whereIn('employee_code', [$sellerUser->employee_code])->first();
                                // $reportingUser = $reportingByCode[$sellerUser->employee_code] ?? null;  
                            }

                            $value->seller_name = credential_decrypt($reportingUser->name) ?? null;
                            $value->seller_mobile = credential_decrypt($reportingUser->mobile) ?? null;
                            $value->seller_type = "Employee";

                        }
                    }
                }


            }

            $col_name = $data->toArray();
        }

        $col_name = !empty($col_name[ 'data' ]) ? $col_name[ 'data' ][ 0 ] : [];
        //excel Download code.....

        if ($request->has('exportNew') && $request->exportNew == true) {
            $excelDownloadLink = '';
            $MisColumnName = empty($MisColumnName) ? array_unique($columnName) : $MisColumnName;

            $dataExportController = new DataExportController();
            $excelDownloadLink = $dataExportController->export($dataQuery, $MisColumnName, $request->template_id,$queryStartDate, $queryEndDate) ?? '';
            if ($excelDownloadLink[ 'status' ] == "pending") {
                return ([
                    'status' => 'pending',
                    'isEmail' => true,
                    'excelExport' => $excelDownloadLink[ 'Message' ] ?? ""
                ]);
            } else {
                return ([
                    'excelExport' => $excelDownloadLink[ 'download_link' ] ?? ''
                ]);
            }
        } elseif (!empty($templateId)) {
            $MisReportColumn = MisReportConfigurator::select('columns', 'static_columns')
                ->where('mis_report_configurator_id', $templateId)
                ->orderBy('sequence')
                ->first();

        $MisColumnName = [];
        
        if ($MisReportColumn) {
        
            $dynamicCols = json_decode($MisReportColumn->columns, true) ?? [];
            $staticCols  = json_decode($MisReportColumn->static_columns, true) ?? [];
        
            // Properly normalize Mongo / Eloquent data
            $data = collect($data)->map(function ($row) {
                return is_object($row) && method_exists($row, 'toArray')
                    ? $row->toArray()
                    : (array) $row;
            })->values()->toArray();
        
            // Column list only once
            $MisColumnName = array_values(array_unique([
                ...array_keys($dynamicCols),
                ...array_keys($staticCols),
            ]));
        
            // Single-pass mapping 
            $data = collect($data)->map(function ($row) use ($dynamicCols, $staticCols) {
        
                foreach ($dynamicCols as $key => $sourceKey) {
                    $row[$key] = $row[$sourceKey] ?? null;
                }
        
                foreach ($staticCols as $key => $value) {
                    $row[$key] = $value;
                }
        
                return $row;
            })->toArray();
        
           
            if (config('mis_column_reporting_details') === "true") {
                $data = mis_reporting_data($data, $MisColumnName);
            }

            $data_customer = mis_customer_renewal_popup($data, $queryStartDate, $queryEndDate, $MisColumnName);        
            if(count($data_customer)>0){
                $data = $data_customer;
                $paginationCount = count($data);
            }
        
            if (config('mis_column_value_replace') === "true") {
                $data = collect($data)->map(function ($row) use ($MisColumnName) {
                    foreach ($MisColumnName as $col) {
                        if (array_key_exists($col, $row)) {
                            $row[$col] = mis_replace_single_value($col, $row[$col]);
                        }
                    }
                    return $row;
                })->toArray();
            }
        }

        $column_head = collect($MisColumnName)->map(function ($value) {
        
            $type = 'string';
        
            if (str_contains($value, 'dob') || str_contains($value, 'date')) {
                $type = 'date';
            } elseif (
                str_contains($value, 'age') ||
                str_contains($value, 'year') ||
                str_contains($value, 'capacity')
            ) {
                $type = 'integer';
            } elseif (str_starts_with($value, 'is_')) {
                $type = 'boolean';
            }
        
            return [
                "header" => ucwords(str_replace('_', ' ', $value)),
                "accessorKey" => $value,
                "isActions" => false,
                "type" => $type
            ];
        })->toArray();

        //masking logic
        $data = applyMasking($data, 'frontend');
        return [
            'data' => $data,
            'columnName' => $MisColumnName,
            'paginationCount' => $paginationCount,
            'column_head' => $column_head
        ];

        } else {

        //masking logic
        $data = applyMasking($data, 'frontend');    
            return [
                'data' => $data,
                'stagecount' => $stagecount,
                // 'listCounts' => $listCounts,
                // 'perPage' => $perPage,
                'stageFilter' => $stageFilter,
                'startDate' => $startDate,
                'endDate' => $endDate,
                'filter_value' => $filter_value,
                // 'journeyStage' => $journeyStage,
                // 'lobFilter' => $lobFilter,
                // 'policyType' => $policyType,
                // 'posType' => $posType,
                'col_arr' => $columnData[ 'data' ] ?? '',
                'paginationCount' => $paginationCount,
                // 'column_head' => $column_head_test
                'redirect_insame_tab' => (int)config('redirect_insame_tab',0),
            ];
        }
    }

    public  function employeeListOld(Request $request)
    {
        $request->validate([
            'user_id' => 'array|required',
        ]);

        $user = Auth::user();
  
         $userLowerHierarchy = getuserlowerHierarchy($user->id, $user->usertype);
         $mapped_user_ids = array_column($userLowerHierarchy, 'id');
         $mapped_user_ids[] = $user->id; 
  
        if (!empty($request->user_id) && !in_array($request->user_id[0], $mapped_user_ids)) {
            return ([
                'status' => 500,
            ]);
        }

        if (!empty($request)) {
            $user = Auth::user();
            $dataQuery = User::select('id', 'name', 'usertype','mobile','middle_name','last_name','employee_code');

            if ($request->user_id || $request->user_type) {
                $newuser = User::where('id',$request->user_id)->first();
                if ($newuser->is_admin == "Y" && $newuser->usertype == "1") {
                    $dataQuery = $dataQuery->where('usertype', '1');

                } else{
                    if ($request->user_id) {
                        $dataQuery = $dataQuery->whereIn('reportingto', $request->user_id);
                    }
                    if ($request->user_type) {
                        $userName  = userTypes::select('id', 'name')->where('Identifier', $request->user_type)->get()->toArray();
                        $dataQuery = $dataQuery->whereIn('usertype', ($userName['id'] ?? ''));
                    }}

            } else {

                $dataQuery = $dataQuery->where('usertype', ($user['id'] ?? ''));
            }
            if ($user->usertype == "1" && $request->user_id[0] == $user->id) {
                $dataQuery = $dataQuery->orWhere('employee_code', $user->employee_code);
            }
            if ($request->user_id[0] != $user->id) {
                 $getEmployee_code = User::find($request->user_id[0]);
                 if ($getEmployee_code->usertype == "1") {
                    $dataQuery = $dataQuery->orWhere('employee_code', $getEmployee_code->employee_code);
                }
            }
            $deataildata = $dataQuery->get()->toArray();
            $data = [];
            foreach ($deataildata as $key => $value) {
                $decrypetedName = credential_decrypt($value['name']).'  '.credential_decrypt($value['middle_name']).'  '.credential_decrypt($value['last_name']).' - '.credential_decrypt($value['mobile']);
                $usertype = userTypes::select('name', 'Identifier')->where('id', $value['usertype'])->first();
                if ($user->id !=$value['id']) {
                    if ($request->user_id[0] !=$value['id']) {
                        $data[] = ['id' => $value['id'], 'name' => $decrypetedName, 'usertype' => $usertype['name'], 'identifier' => $usertype['Identifier']];
                    }
                }
            }
        

            if (!empty($data)) {
                return ([
                    'status' => "200",
                    'message' => "Success",
                    'data' => $data
                ]);
            } else {
                return ([
                    'status' => "500",
                    'message' => "Data not found",
                ]);
                }
            } else {
                return ([
                    'status' => "500",
                    'message' => "Something went wrong. Please try again later.",
                ]);
            }
    }

    public function employeeList(Request $request)
    {
        $request->validate([
            'user_id' => 'required|array',
        ]);

        $authUser = Auth::user();
        $userId = $request->user_id[0] ?? null;
        $userStatus = $request->user_status;

        $userLowerHierarchy = getuserlowerHierarchy($authUser->id, $authUser->usertype, $userStatus);
        $mapped_user_ids = array_column($userLowerHierarchy, 'id');
        $mapped_user_ids[] = $authUser->id;

        if ($userId && !in_array($userId, $mapped_user_ids)) {
            return [
                'status' => 500,
                'message' => 'Unauthorized user access'
            ];
        }

        $userTypes = userTypes::select('id', 'name', 'Identifier')->get()->keyBy('id');

        $selectedUser = null;
        if ($userId) {
            $selectedUser = User::select('id', 'employee_code', 'usertype', 'is_admin')
                ->find($userId);
        }

        $query = User::select('id', 'name', 'middle_name', 'last_name', 'mobile', 'usertype', 'employee_code', 'reportingto');

        if ($userStatus !== 'All') {
            $query->where('status', $userStatus);
        }

        $query->where(function ($q) use ($request, $selectedUser, $userId, $authUser) {

            if ($selectedUser && $selectedUser->is_admin == "Y" && $selectedUser->usertype == "1") {
                $q->where('usertype', '1');
                return;
            }

            if ($userId) {
                $q->where('reportingto', $userId);
            }

            if ($request->user_type) {
                $typeIds = userTypes::where('Identifier', $request->user_type)->pluck('id')->toArray();
                $q->whereIn('usertype', $typeIds);
            }
        });

        $employeeCode = null;

        if ($authUser->usertype == "1" && $userId == $authUser->id) {
            $employeeCode = $authUser->employee_code;
        } elseif ($selectedUser && $selectedUser->usertype == "1") {
            $employeeCode = $selectedUser->employee_code;
        }

        if ($employeeCode) {
            $query->orWhere(function ($q) use ($employeeCode) {
                $q->where('employee_code', $employeeCode);
            });
        }

        $users = $query->get();

        $data = [];

        foreach ($users as $user) {

            if ($user->id == $authUser->id || $user->id == $userId) {
                continue;
            }

            $name = trim(
                credential_decrypt($user->name) . ' ' .
                credential_decrypt($user->middle_name ?? '') . ' ' .
                credential_decrypt($user->last_name ?? '')
            );

            $mobile = credential_decrypt($user->mobile);

            $type = $userTypes[$user->usertype] ?? null;

            $data[] = [
                'id' => $user->id,
                'name' => $name . ' - ' . $mobile,
                'usertype' => $type->name ?? '',
                'identifier' => $type->Identifier ?? ''
            ];
        }

        return !empty($data)
            ? [
                'status' => 200,
                'message' => 'Success',
                'data' => $data
            ]
            : [
                'status' => 500,
                'message' => 'Data not found'
            ];
    }


    public  function filterData(Request $request)
    {


        $stagecount = [];
        $filters = [];
        $stageName = [];
        $perPage = 10;
        $renewalFilter = substagemaster::select('sub_stage_name')->where('is_renewal', 'Y')->get();
        $renewalFilters = $renewalFilter->pluck('sub_stage_name')->toArray();


        $stageMasterModel = StagemasterModel::select('stage_name')->orderby('priority')->get();
        foreach ($stageMasterModel as $value) {
            array_push($stageName, $value['stage_name']);
        }
        $filters = array_unique($stageName);
        foreach ($filters as  $value) {
            $stageMasterModel = StagemasterModel::where('stage_name', $value)->orderBy('priority', 'asc')->first();
            $substageValue = $stageMasterModel->sub_stage_name ?? '';
            $stageData = substagemaster::select('id', 'sub_stage_name')->whereIn('id', explode(",", $substageValue))->get();

            $stageData = substagemaster::select('sub_stage_name')->whereIn('id', explode(",", $substageValue))->get();
            foreach ($stageData as $stageVal) {
                $temp = $stageVal['sub_stage_name'];
            }
            $uniqueStageData[] = $temp ?? '';

            $uniqueStage = array_intersect($renewalFilters, $uniqueStageData);


            $stagecount[$value] = 0;

            // if ($isRenewal) {
            //     if (empty($uniqueStage)) {
            //     } else {
            //         $stagecount[$value] = 0;
            //     }
            // } else {
            //     $stagecount[$value] = 0;
            // }
            foreach ($stageData as $substagedata) {
                $substageData[] = $substagedata['sub_stage_name'] ?? '';
                $stagecountQuery =  MongoModel::where('transaction_stage', $substagedata['sub_stage_name']);
                if (!empty($request['lobFilter'])) {
                    $stagecountQuery = $stagecountQuery->where('section', $request['lobFilter']);
                }
                // if ($isRenewal) {
                //     $keyExist = array_intersect($renewalFilters, ($substagedata->toArray()));
                //     $stagecountQuery = $stagecountQuery->whereIn('transaction_stage', $keyExist);
                // }

                $subStageCount = $stagecountQuery->count();
                if (empty($stagecount)) {
                } else {
                    $stagecount[$value] += $subStageCount;
                }
            }
        }
        // dd($stagecount);
        if (!empty($stagecount)) {
            return response()->json([
                'status' => "200",
                'data' => $stagecount
            ]);
        } else {
            return response()->json([
                'status' => "500",
                'message' => "No Data Found",
            ]);
        }
    }

    public  function columnData(Request $request)
    {
        $defaultCol = [];
        $selectedCol = [];
        $user = Auth::user();
        $roleId = Auth::user()->roles['0']->id;
        //code for get default column

        // $defaultCol = PolicystatusColumnMaster::select('policystatus_column_master.id', 'policystatus_column_master.alias', 'policystatus_column_master.column_name', 'policy_status_column_relation_masters.data_sequence')
        // ->join('policy_status_column_relation_masters', 'policystatus_column_master.id', '=', 'policy_status_column_relation_masters.column_id')
        // ->where('policystatus_column_master.is_default', 'Y')
        // ->get()->toArray();

        $defaultCol = PolicystatusColumnMaster::select('id', 'column_name', 'alias','order_by')->where('is_default', 'Y')->get()->toArray();

        //code for get selected column
        $resultsDatatQuery = PolicystatusColumnMaster::select('policystatus_column_master.column_name', 'policystatus_column_master.id', 'policystatus_column_master.alias','policystatus_column_master.order_by', 'policy_status_column_relation_masters.data_sequence')
        ->join('policy_status_column_relation_masters', 'policystatus_column_master.id', '=', 'policy_status_column_relation_masters.column_id')
        ->where('policy_status_column_relation_masters.status', 'Y')
        ->where('policystatus_column_master.is_visible', 'Y');

        if (!empty($request->section_type)) {
            $lob = lob_master::select('id')->where('lob', $request->section_type)->first();
            $resultsDatatQuery = $resultsDatatQuery->where('policystatus_column_master.lob', $lob->id);
        }
        if (!empty($request->user_id)) {
            $resultsDatatQuery = $resultsDatatQuery->where('policy_status_column_relation_masters.user_id', $request->user_id);
        } else {
            $resultsDatatQuery = $resultsDatatQuery->where('policy_status_column_relation_masters.user_id', $user['id']);
        }
        if (!empty($request->role_id)) {
            $resultsDatatQuery = $resultsDatatQuery->where('policy_status_column_relation_masters.role_id', $request->role_id);
        } else {
            $resultsDatatQuery = $resultsDatatQuery->where('policy_status_column_relation_masters.role_id', $roleId ?? '');
        }
        $resultsData = $resultsDatatQuery->orderBy('data_sequence')->get();
        foreach ($resultsData as $key => $value) {
            $selectedCol[] = [
                "id" => $value['id'],
                "sequence_id" => $value['data_sequence'],
                "column_name" => $value['column_name'],
                "alias" => $value['alias'],
                "order_by" => $value['order_by'] ?? null 
            ];
        }
        $uniquedefaultColumns = collect($defaultCol)->unique('column_name')->values()->all();
        $uniquedeSelectedColumns = collect($defaultCol)->unique('column_name')->values()->all();

        $data = [
            "default_column" => $uniquedefaultColumns,
            "selected_column" => $uniquedeSelectedColumns,
            "all_column" => $uniquedefaultColumns + $uniquedeSelectedColumns
        ];

        $sortFn = fn($a, $b) => ($a['order_by'] ?? 9999) <=> ($b['order_by'] ?? 9999);

        usort($data['default_column'], $sortFn);
        usort($data['selected_column'], $sortFn);

        // Loop through each item in selected_column

        $data['selected_column'] = array_filter($data['selected_column'], function ($selectedItem) use ($data) {
            foreach ($data['default_column'] as $defaultItem) {
                if ($selectedItem['id'] === $defaultItem['id']) {
                    return false;
                }
            }
            return true;
        });

        $data['selected_column'] = array_values($data['selected_column']);


        if (!empty($defaultCol) || !empty($selectedCol)) {
            return ([
                'status' => "200",
                'data' => $data
            ]);
        } else {
            return ([
                'status' => "500",
                'message' => "No Data Found",
            ]);
        }
    }

    public  function columnDataUpdate(Request $request) {
        $add_default = $request->add_default;
        $remove_default = $request->remove_default;
        $sequence_default = $request->sequence_default ?? '';
        $addCol = $removeCol = $Delresponse = $response = $sequenceCol = [];
        $data = [];
        // for updating data
        if (!empty($add_default)) {
            foreach ($add_default as $key => $value) {
                $user_id = auth::user()->id ?? $request->user_id ?? 0;
                $role_id = auth::user()->role_id ?? $request->role_id ?? 0;

                $existingRecord = policy_status_column_relation_master::where([
                    ['column_id', '=', $key],
                    ['user_id', '=', $user_id],
                    ['role_id', '=', $role_id],
                    ['status', '=', 'Y']
                ])->first();

                if (!$existingRecord) {
                    $newRecords[] = [
                        'column_id' => $key,
                        'user_id' => $user_id,
                        'role_id' => $role_id,
                        'status' => 'Y',
                    ];
                }
                if (!empty($newRecords)) {
                    $data = policy_status_column_relation_master::insert($newRecords);
                }
            }
            if ($data) {
                $response = ([
                    'status' => "200",
                    'message' => "Data Added Successfully",
                ]);
            } else {
                $response = ([
                    'status' => "500",
                    'message' => "Data Added Failed",
                ]);
            }
        $addCol =  requestResponseMessage($response);
        } else {
            $addCol = requestResponseMessage($response);
        }
        // for deleting data
        if (!empty($remove_default)) {
            foreach ($remove_default as $key => $value) {
                $data = policy_status_column_relation_master::find($value);
                if (!empty($data)) {
                    $data->status = 'N';
                    $data->save();
                    $Delresponse = ([
                        'status' => "200",
                        'message' => "Data Added Successfully",
                    ]);

                } else {
                    $Delresponse  = ([
                        'status' => "500",
                        'message' => "No Data Found",
                    ]);

                }
            }
            $removeCol  = requestResponseMessage($Delresponse);

        } else {
            $removeCol  = requestResponseMessage($Delresponse);
        }

        // add sequence to the column


    }

    public  function column_master(Request $request)
    {
        $selLob = $request->lob_sel ?? [];
        $selStage = $request->sel_stage ?? [];
        $lobs = lob_master::where('is_enabled', 'Y')->get(['id', 'lob']);

        $allColumns = DB::table('policystatus_column_master')
            ->select('id', 'column_name', 'alias', 'is_default', 'lob', 'stage', 'is_visible', 'order_by')
            ->orderBy('order_by', 'asc') 
            ->get();

        $newData = [];

        foreach ($allColumns as $column) {
            $columnName = $column->column_name;

            if (!isset($newData[$columnName])) {
                $newData[$columnName] = [
                    'id' => $column->id,
                    'column_name' => $columnName,
                    'alias' => $column->alias,
                    'order_by' => $column->order_by, 
                    'is_default' => $column->is_default == 'Y' ? 'Y' : 'N',
                    'is_visible' =>'N',
                    'lob' => $column->is_default == 'Y' ? [$column->lob] : [],
                    'stage' => $column->is_default == 'Y' ? [$column->stage] : [],
                ];
            } else {
                if ($column->is_default == 'Y') {
                    $newData[$columnName]['is_default'] = 'Y';
                    $newData[$columnName]['lob'][] = $column->lob;
                    $newData[$columnName]['stage'][] = $column->stage;
                }
            }
        }

        foreach ($newData as &$data) {
            $data['lob'] = implode(',', array_unique($data['lob']));
            $data['stage'] = implode(',', array_unique($data['stage']));
        }


        if (empty($newData)) {
            return redirect()->back()->with('error', 'No data found');
        }

        $Mstages = StagemasterModel::select('id', 'stage_name')->get();

        return view('column_config_policy_status', compact('newData', 'lobs', 'selLob', 'Mstages', 'selStage'));
    }
    public static function update_column_master(UpdtColumnMaster $request)
    {
        $column_name = $request->column_name;
        $alias =  $request->alias;
        $newOrder = max(1, (int)$request->order_by);
        $update_column = DB::table('policystatus_column_master')
            ->where('column_name', $column_name)
            ->first();

        if (!$update_column) {
            return json_encode([
                'status' => "false",
                'message' => "Column not found"
            ]);
        }


        DB::beginTransaction();

        try {
            DB::table('policystatus_column_master')
                ->where('column_name', $column_name)
                ->update(['order_by' => 0]);

            DB::table('policystatus_column_master')
                ->where('order_by', '>=', $newOrder)
                ->increment('order_by');

            DB::table('policystatus_column_master')
                ->where('column_name', $column_name)
                ->update([
                    'alias' => $alias,
                    'order_by' => $newOrder
                ]);

            DB::commit();

            return json_encode([
                'status' => "true",
                'message' => "Column Updated Successfully"
            ]);

        } catch (\Exception $e) {
            DB::rollBack();

            return json_encode([
                'status' => "false",
                'message' => $e->getMessage()
            ]);
        }
    }
    public static function Enable_columns(EnableCols $request)
    {

        $columnId = $request->col_names;
        $selectedLobs = (array) $request->lob_sel;
        $selectedStages = (array) $request->sel_stage;

        $existingData = DB::table('policystatus_column_master')
            ->select('lob', 'stage')
            ->where('id', $columnId)
            ->first();

        $existingLobs = !empty($existingData->lob) ? explode(",", $existingData->lob) : [];
        $existingStages = !empty($existingData->stage) ? explode(",", $existingData->stage) : [];

        if ($request->action == 'add') {
            $newLobs = array_unique(array_merge($existingLobs, $selectedLobs));
            $newStages = array_unique(array_merge($existingStages, $selectedStages));
        } elseif ($request->action == 'remove') {
            $newLobs = array_diff($existingLobs, $selectedLobs);
            $newStages = array_diff($existingStages, $selectedStages);
        } else {
            return response()->json([
                'status' => "false",
                'message' => "Invalid action"
            ]);
        }

        $update = DB::table('policystatus_column_master')
            ->where('id', $columnId)
            ->update([
                'lob' => implode(",", $newLobs),
                'stage' => implode(",", $newStages),
                'is_visible' => ($request->action == 'add') ? 'Y' : 'N'
            ]);

        if ($update) {
            return response()->json([
                'status' => "true",
                'message' => "Column updated successfully",
                'data' => [
                    'lob' => implode(",", $newLobs),
                    'stage' => implode(",", $newStages)
                ]
            ]);
        }

        return response()->json([
            'status' => "false",
            'message' => "Database update failed"
        ]);
    }

    public static function set_default(Request $request)
    {
        $valid = $request->validate([
           'is_default' => 'required|string|in:Y,N',
            'column_name' => 'required|string',
            'lob_sel' => 'required|array',
            'stage_sel' => 'required|array'
        ]);


            $column_name = $request->column_name;
            $is_default = $request->is_default;
            $lob_ids = $request->lob_sel;
            $stage_ids = $request->stage_sel;

            $stage_str = implode(',', $stage_ids);
            
            $existingLobCount = DB::table('policystatus_column_master')->where('column_name', $column_name)->whereIn('lob', $lob_ids)->count();
            if ($existingLobCount === 0) {
                return response()->json(['status' => "false", 'message' => "Invalid LOB selection"]);
            }

            $update_column = DB::table('policystatus_column_master')
                ->where('column_name', $column_name)
                ->whereIn('lob', $lob_ids)
                ->update([
                    'is_default' => $is_default,
                    'stage' => $stage_str 
                ]);


            if ($update_column) {
                return response()->json([
                    'status' => "true",
                    'message' => "Column Updated Successfully"
                ]);
            } else {
                return response()->json([
                    'status' => "false",
                    'message' => "Update failed. No rows were affected."
                ]);
            }
    }


    public static function MisReportFilter(Request $request) {

        $motorFetchService = new MotorFetchService();
        $selectedLobValues = $request->input('lob_values', []);
        $stageFilterarray = $motorFetchService->stageFilter();
        $stageFilter = $stageFilterarray[0];

        if (!empty($stageFilter)) {

            return ([
                "status" => 200,
                "stageFilter" => $stageFilter
            ]);
        } else {

            return ([
                "status" => 500,
                "stageFilter" => "No Data Found"
            ]);
        }


    }

    public  function MisReportData(Request $request)  {

        $viewPermision = "Report.view";
        $user = Auth::user();
        if (!$user->can($viewPermision)) {
            return ([
                "status" => 403,
                "message" => "You don't have permission to view this report"
            ]);
        }
        if (!empty($request)) {
            if (empty($request->template_id)) {
                return ([
                    "status" => 500,
                    "message" => "Template ID  Found"
                ]);

            }
            $data = self::stages($request);
            if (!empty($data)) {
                $maxCountLimit = config('excel.data.limit.download');
                return $data;
            } else {

                return ([
                    "status" => 500,
                    "message" => "No Data Found"
                ]);
            }

        }  else {
            return ([
                "status" => 500,
                "message" => "No Data Found"
            ]);
        }


    }
    public function policyDetails(Request $request){

        $user = Auth::user();

        $listingPermission = "Policy Status.view";
        if (!$user->can($listingPermission)) {
            return response()->json([
                'status' => false,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }
        
        $result = MongoModel::whereIn('seller_id', [$request->user_id])
                        ->where('section', 'term')
                        ->orderBy('_id', 'desc')
                        ->first();

        $investment_result = MongoModel::whereIn('seller_id', [$request->user_id])
                        ->where('section', 'investment')
                        ->orderBy('_id', 'desc')
                        ->first();

        $policy_result = MongoModel::whereIn('seller_id', [$request->user_id])
                        ->whereIn('transaction_stage', ['Policy Issued','Policy Issued pdf generated','Policy Issued, but pdf not generated'])
                        ->orderBy('_id', 'desc')
                        ->get()->toArray();

        if(empty($result) && empty($investment_result) && empty($policy_result)){

            return response()->json([
                'status' => 'false',
                'message' => 'Data Not found'
            ], 200);
        }else{
            if ($result) {
                $output []= $result->toArray();
            }

            if ($investment_result) {
                $output[] = $investment_result->toArray();
            }

            if ($policy_result) {
                $output[] = $policy_result->toArray();
            }

        return response()->json([
                            'status' => 'true',
                            'message' => 'Data Found.',
                            'data' => $output
                        ], 200);
                    }
    }



    public function premiumFilter(Request $request){

        $AccessorKey= $request->accessorKey;
        $structuredData = [];
        foreach($AccessorKey as $akey){

            $requestedData = MongoModel::select($akey['key'])
            ->where($akey['key'], '!=', '') // Exclude empty strings
            ->where($akey['key'], '!=', ' ') // Exclude spaces-only strings
            ->limit($akey['page_size'])
            ->get();


            $requestedData->each(function ($item) {
                unset($item['id']);
            });

             $newData=$requestedData->toArray();

             $inc = 1;
             foreach ($newData as $item) {
                $id = $inc++;
                foreach ($item as $key => $value) {

                    if(!empty(trim($value))){   //This condition is to for not pushing empty values
                        $structuredData[$key][] = [
                            'id' => $id,
                            'name' => $value,
                            'value' => $value
                        ];
                    }


                }
            }

        }


          return response()->json($structuredData);

     }

     public function getPolicyDetailsByCustomerMobile(Request $request)
    {
        $request->validate(
            ['mobile_no' => 'required|digits:10'],
            ['mobile_no.digits' => 'Mobile number must be exactly 10 digits']
        );
        $mobile_no = strval($request->mobile_no);
    
        $subStagesArr = ['Policy Issued','Policy Issued pdf generated'];
    
        $query = MongoModel::select(
            'trace_id', 'proposer_name', 'proposer_mobile', 'proposer_emailid','proposer_gender','proposer_dob','pincode','address_line_1',
            'address_line_2', 'address_line_3', 'state', 'city', 'vehicle_registration_number', 'company_name', 'transaction_stage',
            'product_name', 'proposal_no', 'policy_no', 'proposal_url', 'section', 'policy_type', 'engine_number', 'chassis_number',
            'vehicle_make','vehicle_model', 'vehicle_version', 'vehicle_fuel_type', 'quote_url', 'company_logo_url', 'policy_term',
            'cpa_policy_start_date', 'cpa_policy_end_date', 'nominee_dob', 'nominee_relationship', 'nominee_age', 'nominee_name',
            'tp_start_date', 'tp_end_date', 'owner_type', 'product_type', 'sub_product_type', 'renewal_redirection_url',
            'policy_start_date', 'policy_end_date', 'user_id', 'lastupdated_time', 'seller_id', 'seller_type','policy_doc_path'
        )->whereIn('transaction_stage', $subStagesArr)->where('proposer_mobile', $mobile_no);
    
        // if (!empty($seller_type)) {
        //     $query->where('seller_type', $seller_type);
        // }
    
        $data = $query->get();
    
        if ($data->isEmpty()) {
            return response()->json([
                'message' => 'Data not found',
            ], 404);
        }
        foreach ($data as $value) {
            if (!empty($value->policy_doc_path) && config('s3_download_link') == true) {
                $parsedUrl = parse_url($value->policy_doc_path);
                
                if (!empty($parsedUrl['path'])) {
                    $fileKey = ltrim($parsedUrl['path'], '/'); 
            
                    $value->policy_doc_path = Storage::disk('s3')->temporaryUrl(
                        $fileKey,
                        now()->addDays(7)
                    );
                }
            }
        }
    
        return response()->json([
            'message' => 'Success',
            'data' => $data,
        ], 200);
    }

    public function getInspectionStatus(Request $request)
    {
        $request->validate(
            ['inspection_no' => 'required|string']
        );
        $url = config('Inspection_check_api');
        $inspection_request = ['inspectionNo' => $request->inspection_no];
        
        if(config('fetch_sp_details')){
            $response = Http::timeout(30)
            ->withHeaders(['Origin' => $request->headers->get('origin')])
            ->post($url, $inspection_request);    
        }else{
            $response = Http::timeout(30)
            ->post($url, $inspection_request);    
        }
    
        return response()->json([
            'message' => $response['msg']
        ], 200);
    }

 }

