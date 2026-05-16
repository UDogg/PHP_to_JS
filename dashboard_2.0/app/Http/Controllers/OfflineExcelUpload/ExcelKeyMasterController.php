<?php

namespace App\Http\Controllers\OfflineExcelUpload;

use App\Exports\ExcelKeyExport;
use App\Exports\ExcelKeyMasterExport;
use App\Http\Controllers\Controller;
use App\Http\Requests\SanitizeExcelColumnRequest;
use App\Imports\ExcelUploadImport;
use App\Models\ExcelKeyMaster;
use App\Models\OfflineExcelUploadData;
use App\Models\PolicyStatusColumnMaster;
use Illuminate\Http\Request;
use App\Models\lobMaster;
use App\Models\User;
use App\Models\StagemasterModel;
use Carbon\Carbon;
use Exception;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Http;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;
use App\Models\MongoModel; 
use PhpOffice\PhpSpreadsheet\Shared\Date;

use App\Exports\OfflinePolicySampleExport; 
use Illuminate\Support\Facades\Validator;
use App\Services\ExcelUploadService;


class ExcelKeyMasterController extends Controller
{
    protected $auth;
    public function __construct()
    {
        $this->auth = Auth::user();
    }
    public function get_column_lob_wise(Request $request){
        $lob=lobMaster::where('lob_master_name',$request->lob_name)->first();
        $policy_status_master = PolicyStatusColumnMaster::leftJoin('excel_key_master', 'policystatus_column_master.id', '=', 'excel_key_master.policystatus_column_master_id')
            ->where('lob', $lob->id)
            ->select('policystatus_column_master.id','policystatus_column_master.column_name', 'policystatus_column_master.alias', 'excel_key_master.is_visible', 'excel_key_master.excel_column_name')
            ->get();
        $unique_results = $policy_status_master->unique('column_name')->values();
        return response()->json([
            'status' => "true",
            'return_data' => $unique_results,
            'message' => "Data Found"
        ]);
    }
    public  function column_master(Request $request)
    {
        $selLob = $request->lob_sel;
        $selStage = $request->sel_stage;
        $lobs = lobMaster::select('lob', 'id')->where('is_enabled', 'Y')->get()->all();
        $allColumns = DB::table('policystatus_column_master')->select('column_name', 'lob', 'alias', 'id', 'is_visible', 'is_default', 'stage');
        $allColumns = !empty($selLob) ? $allColumns->where('lob', $selLob) : $allColumns;
        $allColumns = $allColumns->get();
        $checkColumns = array_column($allColumns->toArray(), 'column_name');
        $checkColumnSection = array_unique(array_column($allColumns->toArray(), 'section'));
        $allColumns2 = $allColumns->pluck('column_name')->all();
        $Mstages = StagemasterModel::select('id', 'stage_name')->get();
        if (empty($allColumns)) {
            return  redirect()->back()->with('error', 'No data found');
        } else {
            return view('excelupload.excel_key_master', compact('allColumns', 'lobs', 'selLob', 'Mstages', 'selStage'));
        }
    }
    public static function AddColumnToExcel(Request $request)
    {
        $selLob = $request->lob_sel;
        $column = $request->col_names;
        $column_id = $request->id;
        if ($request->action == 'add') {
            $check = ExcelKeyMaster::where('policystatus_column_master_id', $column_id)
            ->where(function($query) {
                $query->whereIn('is_visible', ['Y', 'N'])
                      ->orWhereNull('is_visible');
            })
            ->exists();
            
            if($check == true){
                $InsertColumn = ExcelKeyMaster::where('policystatus_column_master_id', strval($column_id))->update([
                    'is_visible' => 'Y',
                ]);
                if ($InsertColumn) {
                    return response()->json([
                        'status' => "true",
                        'message' => "Column Is visible Successfully"

                    ]);
                } else {
                    return response()->json([
                        'status' => "false",
                        'message' => "Something went wrong"
                    ]);
                }
            }
            if ($check == false) {
                $InsertColumns = ExcelKeyMaster::insert([
                    'policystatus_column_master_id' => $column_id,
                    'excel_column_name'=>$column,
                    'lob_id' => $selLob,
                    'is_visible' => 'Y',
                ]);
                if ($InsertColumns) {
                    return response()->json([
                        'status' => "true",
                        'message' => "Column Added Successfully"

                    ]);
                } else {
                    return response()->json([
                        'status' => "false",

                        'message' => "Something went wrong"
                    ]);
                }
            } else {
                return response()->json([
                    'status' => "false",

                    'message' => "Data already exists"
                ]);
            }
        } elseif ($request->action == 'remove') {
            $updateColumn = ExcelKeyMaster::where('policystatus_column_master_id', strval($column_id))->update([
                'is_visible' => 'N',
                'deleted_at' => Carbon::now(),
            ]);
            if ($updateColumn) {
                return response()->json([
                    'status' => "true",
                    'message' => "Column removed Successfully"

                ]);
            } else {
                return response()->json([
                    'status' => "false",
                    'message' => "Something went wrong"
                ]);
            }
        }
    }

    public function excel_column_master(Request $request)
    {
         $excelEditAddPermission = 'Offline Excel Configurator.view';

        if (!$this->auth->hasPermissionTo($excelEditAddPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $lobs = lobMaster::select('lob', 'id')->get()->all();
        $lob_id = $request->lob_id;
        // $lob_name = $request->lob_name;
        $allColumns = ExcelKeyMaster::with('policyStatusColumns')
        ->where('is_visible', 'Y')
        ->where('lob_id', $lob_id)
        ->get()
        ->map(function ($column) {
            return [
                'excel_key_master_id' => $column->excel_key_master_id,
                'policystatus_column_master_id' => $column->policystatus_column_master_id,
                'excel_column_name' => $column->excel_column_name,
                'sequence' => $column->sequence,
                'sample_data' => $column->sample_data,
                'key_name' => optional($column->policyStatusColumns)->column_name
            ];
        })
        ->toArray(); 

        $sampleData = \App\Models\SampleData::first();
        $matchedData = [];

        // if ($sampleData) {
        //     $value = json_decode($sampleData->value, true);
        //     foreach ($allColumns as $column) {
        //         $columnName = $column->column_name;
        //         if (array_key_exists($columnName, $value)) {
        //             $matchedData[$columnName] = $value[$columnName];
        //         }
        //     }
            
        //    if (isset($matchedData['_id']) && is_object($matchedData['_id'])) {
        //         $matchedData['_id'] =$matchedData['_id']['$oid'] ;
        //     } 
    
        //     foreach ($value as $key => $val) {
        //         if (is_object($val)) {
        //             foreach ($val as $subKey => $subVal) {
        //                 if (!isset($matchedData[$key])) {
        //                     $matchedData[$key] = [];
        //                 }
        //                 $matchedData[$key][] = [$subKey => $subVal]; 
        //             }
        //         }
        //     }
        // }
    
        // array_walk_recursive($matchedData, function (&$item) {
        //     if (is_object($item)) {
        //         $item = (array) $item;
        //     }
        // });
    
        if ($request) {
            return response()->json([
                'allColumns' => $allColumns,
                'matchedData' => $matchedData,
            ]);
        }else{
            return view('excelupload.excel_key_show', compact('lobs', 'allColumns'));
        }
       
    }
    
    public static function UpdateColumnNameToExcel(Request $request)
    {
        if (!auth()->user()->can('Offline Excel Configurator.upload')) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }

        $columnIds = $request->excel_key_master_id;
        $sequences = $request->sequence;
        $aliases = $request->excel_column_name;
        $sampleData = $request->sample_data;

        $updated = false;

        foreach ($columnIds as $key => $id) {
            $updateData = [];

            if (isset($sequences[$key])) {
                $updateData['sequence'] = $sequences[$key];
            }

            if (isset($aliases[$key])) {
                $updateData['excel_column_name'] = $aliases[$key];
            }

            if (isset($sampleData[$key])) {
                $updateData['sample_data'] = $sampleData[$key];
            }

            if (!empty($updateData)) {
                $updateColumn = ExcelKeyMaster::where('excel_key_master_id', $id)->update($updateData);
                if ($updateColumn) {
                    $updated = true;
                }
            }
        }

        if ($updated) {
            return response()->json([
                'status' => 'true',
                'message' => 'Column Updated Successfully'
            ]);
        } else {
            return response()->json([
                'status' => 'false',
                'message' => 'No Data Found in Key Column Master'
            ]);
        }
    }

    public function excelColumnAdd(SanitizeExcelColumnRequest $request)
    {
        $excelEditAddPermission = 'Offline Excel Configurator.edit';

        if (!$this->auth->hasPermissionTo($excelEditAddPermission)) {
            return requestResponseMessage(['status' => 403, 'message' => 'Access Denied']);
        }
        
        $columnMaster = PolicystatusColumnMaster::where('column_name', $request->policystatus_column_master_id)->first();

        if (!$columnMaster) {
            $columnMaster = new PolicystatusColumnMaster();
            $columnMaster->column_name = $request->policystatus_column_master_id;
            $columnMaster->save();
        }

        $excel = new ExcelKeyMaster();
        $excel->policystatus_column_master_id = $columnMaster->id; 
        $excel->excel_column_name = $request->excel_column_name;
        $excel->sequence = $request->sequence;
        $excel->sample_data = $request->sample_data;
        $excel->is_visible = 'Y';
        $excel->lob_id = $request->lob_id;
        $excel->save();

        return response()->json([
            'status' => 200,
            'message' => 'Column Added Successfully'
        ]);
    }

    public function DownloadExcel(Request $request)
    {
        $lob_id = $request->input('lob_id');
        $lob = lobMaster::select('lob','is_enabled')->where('id', $lob_id)->first();
        if ($lob->is_enabled !== 'Y') {
            return response()->json([
                'status' => '500',
                'message' => 'LOB is not active.'
            ], 500);
        }
        $lob_name = $lob->lob;
        $dataExists = ExcelKeyMaster::where('lob_id', $lob_id)->exists();
        if (!$dataExists) {
            return response()->json([
                'status' => '500',
                'message' => 'No Data Found in Excel'
            ]);
        } else {
            $excelFileName = $lob_name . '_' . date('Y_m_d') . '_' . time() . '.xlsx';
            Excel::store(new ExcelKeyMasterExport($lob_id), $excelFileName, 'public');
            $fileUrl = Storage::disk('public')->url($excelFileName);
            return response()->json([
                'status' => '200',
                'message' => 'File is ready for download.',
                'download_link' => $fileUrl,
            ], 200);
        }
    }
    public function UploadExcel(Request $request, ExcelUploadService $service)
    {
        $excelUploadPermision = 'Offline Policy Upload.upload';
        if (!$this->auth->can($excelUploadPermision)) {
            return response()->json(['status' => 403, 'message' => 'Access Denied'], 403);
        }

        // Call the service to handle the upload
      return $service->processExcelUpload($request);    

    }
    public function import(Request $request)
    {
        $lob_id = $request->input('lob_id');
        $request->validate([
            'excel_upload' => 'required|mimes:xlsx,xls,csv',
        ]);

        $import = new ExcelUploadImport($lob_id);

        Excel::import($import, $request->file('excel_upload'));
        $data = $import->getData();
        unset($data[0]);
        return $data;
    }
    public function listExcelFile()
    {
        $excelUploadData = OfflineExcelUploadData::orderBy('created_at', 'desc')->select('offline_excel_upload_data_id','excel_file_name','total_record','failed_record','success_record','created_at','updated_at','lob_id')->get();
        if ($excelUploadData->isNotEmpty()) {
            $formattedData = $excelUploadData->map(function ($item) {
                $itemArray = $item->toArray();
                $itemArray['created_at'] = Carbon::parse($item->created_at)->format('Y-m-d'); 
                $itemArray['updated_at'] = Carbon::parse($item->updated_at)->format('Y-m-d'); 
                return $itemArray;
            });
            $paginationCount = $formattedData->count();
            return response()->json([
                'status' => 200,
                'data' => $formattedData,
                'paginationCount' => $paginationCount,
                'message' => 'Data Found'
            ], 200);
        }
        return response()->json([
            'status' => 500,
            'data' => [],
            'message' => 'No Data Found'
        ], 500);
    }
    
    public function mongoExcelUpload(Request $request)
    {
        $file = $request->file('excel_file');
        $lob_id = (int)$request->input('lob_id');
    
        if (!$file || !$lob_id) {
            return response()->json([
                "status" => 400,
                "message" => "Invalid input data"
            ]);
        }
    
        $parsedData = Excel::toArray([], $file);
        $headerRow = $parsedData[0][0];
        $dataRows = array_slice($parsedData[0], 1); 
        $excelColumns = ExcelKeyMaster::join('policystatus_column_master', 'policystatus_column_master.id', '=', 'excel_key_master.policystatus_column_master_id')
            ->where('lob_id', $lob_id)
            ->pluck('column_name', 'excel_column_name')
            ->toArray();
    
        if (empty($excelColumns)) {
            return response()->json([
                "status" => 404,
                "message" => "Columns are not found for the provided lob_id"
                ]);
            }
        foreach ($dataRows as $row) {
            $mappedRow = [];
            foreach ($excelColumns as $excelCol => $dbCol) {
                $headerIndex = array_search($excelCol, $headerRow);
                $mappedRow[$dbCol] = isset($headerIndex) && isset($row[$headerIndex]) ? $row[$headerIndex] : null;
            }
    
            $insert = MongoModel::insert(array_merge([
                'lob_id' => $lob_id
            ], $mappedRow));
            if ($insert) {
                $insertedRows[] = $mappedRow;
            }
            if (!empty($insertedRows)) {
                return response()->json([
                    "status" => 200,
                    'data' => $insertedRows,
                    "message" => "Data successfully inserted into MongoDB"
                ]);
            } else {
                return response()->json([
                    "status" => 500,
                    "message" => "Failed to insert data into MongoDB"
                ]);
            }
        }
    }


    // public function validateExcelData(){
    //     $url = 'https://uatapimotor.heroinsurance.com/api/renewal-data-upload';
    //     $requestData = [
    //         "policies" => [
    //             [
    //                
    //             ]
    //         ]
    //     ];
    //     $headers = [
    //         'Content-Type' => 'application/json',
    //     ];

    //     // try {
    //         $response = Http::withHeaders($headers)
    //             ->post($url, $requestData);
    //         if ($response->successful()) {
    //             return response()->json([
    //                 'status' => 'success',
    //                 'data' => $response->json()
    //             ]);
    //         } else {
    //             return response()->json([
    //                 'status' => 'error',
    //                 'message' => $response->body()
    //             ], $response->status());
    //         }
    //     // } catch (\Exception $e) {
    //     //     return response()->json([
    //     //         'status' => 'error',
    //     //         'message' => $e->getMessage()
    //     //     ], 500);
    //     // }
    // }

    public function offlinePolicySampleExcel(Request $request)
    {
        $request->validate([
            'lob_id'=> 'required',
        ]);

        $lobId = $request->input('lob_id');
    
        $lob = ExcelKeyMaster::where('lob_id', $lobId)->where('is_visible', 'Y')->first();
    
        if (!$lob) {
            return response()->json([
                'status' => 404,
                'message' => 'Invalid or inactive LOB ID.',
            ], 404);
        }
    
        $columnNames = ExcelKeyMaster::where('lob_id', $lobId)
                                        ->where('is_visible', 'Y')
                                        ->pluck('sample_data', 'excel_column_name')
                                        ->toArray();

        $fileName = 'Offline_Policy_Sample_Excel_' . $lobId . '.xlsx';


        if(config('dashboard_storage_disk') === 's3') $donwloadFrom = 's3';
        else $donwloadFrom = 'public';

        Excel::store(new OfflinePolicySampleExport($columnNames), $fileName, $donwloadFrom);

        if(config('dashboard_storage_disk') === 's3'){
            $fileUrl = Storage::disk('s3')->temporaryUrl($fileName, now()->addMinutes(30));
        }else{
            $fileUrl = Storage::url($fileName);
        }
        
        $masterfilePath = 'offline_upload_sample_excel/Master_Data.xlsx';
        
        if(!Storage::disk('s3')->exists($masterfilePath)){
            return response()->json([
                'status' => 404,
                'message' => 'File Not Found!',
            ], 404);
        }

        if(config('dashboard_storage_disk') === 's3'){
            $masterfilePathUrl = Storage::disk('s3')->temporaryUrl($masterfilePath, now()->addMinutes(30));
        }else{
            $masterfilePathUrl = Storage::url($masterfilePath);
        }

        return response()->json([
            'status' => 200,
            'message' => 'Sample Link',
            'file_url' => $fileUrl,
            'master_file_url'=> $masterfilePathUrl
        ]);
    }
    
}
