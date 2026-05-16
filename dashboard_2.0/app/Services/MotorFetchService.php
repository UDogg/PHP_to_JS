<?php

namespace App\Services;

use App\Http\Requests\StageMaster;
use Carbon\Carbon;
use App\Models\policy;
use App\Models\MongoModel;
use Illuminate\Http\Request;
use App\Models\substagemaster;
use App\Models\StagemasterModel;
use Illuminate\Support\Facades\DB;
use App\Interfaces\PolicyStatusData;
use App\Models\PolicyStatusColumnMaster;
use App\Models\PolicyStatusFilterMaster;
use Illuminate\Pagination\LengthAwarePaginator;
use App\Models\lobMaster;

class MotorFetchService implements PolicyStatusData
{
    public function fetchdata($isRenewal , $selectedLobValues = [])
    {

        $filters = [];
        $stageName = [];
        $perPage = 10;
        $section = [];

        $data = '';
        $count = 0;
        $perPage = 10;
        $columnName = [];
        $oneMonthAgo = Carbon::now()->subMonth();
        $PolicyStatusColumnMasterArray = [];
        $renewalFilter = substagemaster::select('sub_stage_name')->where('is_renewal', 'Y')->get();
        $renewalFilters = $renewalFilter->pluck('sub_stage_name')->toArray();

        $lobValue = lobMaster::all();
        $section = [];
        if (!empty($selectedLobValues)) {
            $section = array_filter(
                $lobValue->pluck('lob')->toArray(),
                fn($lob) => in_array($lob, $selectedLobValues)
            );
        } else {
            foreach ($lobValue as $value) {
                if ($value['is_enabled'] == "Y") {
                    array_push($section, $value['lob']);
                }
            }
        }

        $stagecount = [];
        $stageMasterModelDtata = StagemasterModel::select('stage_name')->orderby('priority')->get();
        foreach ($stageMasterModelDtata as $value) {
            array_push($stageName, $value['stage_name']);
        }
        $filters = array_unique($stageName);
        foreach ($filters as  $value) {
            $stageMasterModel = StagemasterModel::where('stage_name', $value)->orderBy('priority')->first();
            $substageValue = $stageMasterModel->sub_stage_name ?? '';
            $stageData = substagemaster::select('sub_stage_name')->whereIn('id', explode(",", $substageValue))->get();
            foreach ($stageData as $stageVal) {
                $temp = $stageVal['sub_stage_name'];
            }
            $uniqueStageData[] = $temp ?? '';

            $uniqueStage = array_intersect($renewalFilters, $uniqueStageData);



            if ($isRenewal) {
                if (empty($uniqueStage)) {
                } else {
                    $stagecount[$value] = 0;
                }
            } else {
                $stagecount[$value] = 0;
            }
            foreach ($stageData as $substagedata) {
                $substageData[] = $substagedata['sub_stage_name'] ?? '';
                $subStageCountQuery = MongoModel::select('trace_id');
                if ($isRenewal) {
                    $keyExist = array_intersect($renewalFilters, ($substagedata->toArray()));
                    $subStageCountQuery = $subStageCountQuery->whereIn('transaction_stage', $keyExist);
                } else {
                    $subStageCountQuery = $subStageCountQuery->where('transaction_stage', $substagedata['sub_stage_name']);
                }

                $subStageCount = $subStageCountQuery->count();
                if (empty($stagecount)) {
                } else {
                    $stagecount[$value] += $subStageCount;
                }
            }
        }

        $subStageFilterData = [];
        $results = DB::table('stage_master as s')
        ->join('sub_stage_master as m', DB::raw('FIND_IN_SET(m.id, s.sub_stage_name)'), '>', DB::raw('0'))
            ->select('s.stage_name', 'm.sub_stage_name', 's.priority', 's.id')
            ->where('s.priority', 1)
            ->get();
        $stageNameData = $results[0]->id;
        $resultsDataDefault  = PolicyStatusColumnMaster::select('column_name')->where('stage', 'like', '%' . $stageNameData . '%')->where('is_default', 'Y')->get();
        foreach ($resultsDataDefault as $key => $value) {
            $columnName[] = $value['column_name'];
            // $subStageFilterData[] = $value->sub_stage_name;
            $PolicyStatusColumnMasterArray[] = [$value['column_name'] => $value['alias']];
        }
        $resultsData  = PolicyStatusColumnMaster::where('stage', 'like', '%' . $stageNameData . '%')->where('is_visible', 'Y')->get();

        foreach ($resultsData as $key => $value) {
            $columnName[] = $value['column_name'];
            // $subStageFilterData[] = $value->sub_stage_name;
            $PolicyStatusColumnMasterArray[] = [$value['column_name'] => $value['alias']];
        }
        array_push($columnName, 'quote_url', 'proposal_url');
        foreach ($results as $key => $value) {
            $subStageFilterData[] = $value->sub_stage_name;
        }
        $transactionOrder = array_flip($subStageFilterData);
        $dataQuery =  MongoModel::select($columnName)->whereIn('section', $section);
        if ($isRenewal) {
            $renewalFilter = substagemaster::select('sub_stage_name')->where('is_renewal', 'Y')->get();
            $renewalFilters = $renewalFilter->pluck('sub_stage_name')->toArray();
            $keyExist = array_intersect($renewalFilters, $subStageFilterData);
            $dataQuery = $dataQuery->whereIn('transaction_stage', $keyExist);
        } else {
            $dataQuery = $dataQuery->whereIn('transaction_stage', $subStageFilterData);
        }
        $results = $dataQuery->get();
        $paginationCount = count($results);
        // Sort the data in PHP
        $sortedResults = $results->sortBy(function ($item) use ($transactionOrder) {
            return $transactionOrder[$item->transaction_stage] ?? 999;
        })->values();

        // Paginate the sorted data
        $currentPage = LengthAwarePaginator::resolveCurrentPage();
        $perPage = 10;
        $currentResults = $sortedResults->slice(($currentPage - 1) * $perPage, $perPage)->values();

        $paginatedResults = new LengthAwarePaginator(
            $currentResults,
            $sortedResults->count(),
            $perPage,
            $currentPage,
            ['path' => LengthAwarePaginator::resolveCurrentPath()]
        );

        $data = $paginatedResults;
        $col_name  =  $data->toArray();
        $col_name = !empty($col_name['data']) ? $col_name['data'][0] : [];

        $col_arr = [];
        foreach ($PolicyStatusColumnMasterArray as $col_key => $col_val) {

            foreach ($col_val as $key => $value) {
                if (array_key_exists($key, $col_name)) {
                    $col_arr[$key] = $value;
                }
            }
        }

        $count = MongoModel::whereIn('section', $section)->count();
        $filter = self::stageFilter();
        $stageFilter = $filter[0];
        return array($data, $stagecount, $count, $perPage, $stageFilter, $PolicyStatusColumnMasterArray, $col_arr,$paginationCount);
    }
    public function stageFilter()
    {
        $filter = [];
        $filterName = [];

        $allFilters = PolicyStatusFilterMaster::all()->groupBy('filtername');

        foreach ($allFilters as $filtername => $filterItems) {
            $values = [];
            $keys = [];

            foreach ($filterItems as $item) {
                $values[] = $item->type == 3 ? 'date' : $item->value;
                $keys[] = $item->key;
            }

            $filter[$filtername] = array_values(array_unique($values));
            $filterName[$filtername] = array_values(array_unique($keys));
        }

        return [$filter, $filterName];
    }

}
