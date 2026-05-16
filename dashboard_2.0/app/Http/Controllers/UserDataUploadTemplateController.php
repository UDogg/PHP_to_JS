<?php

namespace App\Http\Controllers;

use App\Events\UserexcelDataImport as EventsUserexcelDataImport;
use App\Events\userExcelDataImportEvent;
use App\Events\userExcelDataMappingEvent;
use App\Exports\UserdataUploadError;
use App\Imports\UserdataImport;
use App\Imports\UserMappingReportingTo;
use App\Models\DataExportLog;
use App\Models\QualificationMaster;
use App\Models\User;
use App\Models\userTypes;
use App\Models\ZoneMasterModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Storage;
use Maatwebsite\Excel\Facades\Excel;

class UserDataUploadTemplateController extends Controller
{
    private $Auth;
    private $importedData;
    public function __construct()
    {
        $this->Auth = Auth::user();
    }
    public function ExcelUserUpload(Request $request)
    {
        $permission = "User Creation.upload";
        if (!$this->Auth->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $request->validate([
            'file' => 'required|mimes:xlsx,xls|file|max:26200',
            'type' => ['required',"in:E,P,Partner"],
        ]);
        $userTypeList = userTypes::select('id','Identifier')->get()->toArray();
        $zoneList = ZoneMasterModel::select('id','office_zone')->get()->toArray();
        $QualificationList = QualificationMaster::select('qualification_master_id','qualification_name')->get()->toArray();
        foreach ($userTypeList as $value) {
            if($value['Identifier'] ==  $request->type)
            {
                $usertypehh = $value['id'];
            }
        }
            if ($request->type === 'E') {
                    $AllUsersData = User::select('id','username','mobile','email','adhar_no','pan_no')
                        ->with('roles:id,name')
                        ->where('usertype', 1)
                        ->get();
            } else {
            $AllUsersData = User::select('id','username','mobile','email','adhar_no','pan_no')->with('roles:id,name')->get();
            }
           $decptAllusersData = $AllUsersData->map(function ($user) {
           $user->username =  credential_decrypt($user->mobile);
           $user->mobile = credential_decrypt($user->mobile);
           $user->email = credential_decrypt($user->email);
           $user->adhar_no = credential_decrypt($user->adhar_no);
           $user->pan_no = credential_decrypt($user->pan_no);

           return $user;
        })->toArray();
        $import = new UserdataImport($request,$userTypeList,$zoneList,$QualificationList,$decptAllusersData);
        Excel::import($import, $request->file('file'));
//        need to duplicate this code as want to get fresh instance from db after userdata import into db
        
        $ErrorCount = 0;
        $mappingsErrros = [];
        $randomNumber = rand(1000, 9999);
        if(!empty($import->getErrors()) || !empty($mappingsErrros))
        {
            foreach ($import->getErrors() as  $value) {
                if(!empty($value['errors']))
                {
                    $ErrorCount++;
                }
            }
            $value= null;
            foreach ($mappingsErrros as  $value) {
                if(!empty($value['errors']))
                {
                    $ErrorCount++;
                }
            }
        }

        if($request->type == 'E')
        {
            $path = 'Errors/EmployeeImportError'.$randomNumber.'.xlsx';
            if (count($import->getErrors()) > 0) {
                Excel::Store(new UserdataUploadError($import->getErrors()), $path,'public');
                $this->ExcelLog($this->Auth->id,$path,'UserExportData','completed',$request->all());
                return response()->json([
                   'Status' => 200,
                    'Message' => 'User Data Import Error',
                    'ErrorCount' => $ErrorCount,
                    'TotalCount' => count($import->getImportedData()),
                    'download_link' => Storage::disk('public')->url('Errors/EmployeeImportError'.$randomNumber.'.xlsx'),
                ]);
            }
            if(count($mappingsErrros) > 0)
            {
                Excel::Store(new UserdataUploadError($mappingsErrros), 'Errors/EmployeeImportError'.$randomNumber.'.xlsx','public');
                $this->ExcelLog($this->Auth->id,'Errors/EmployeeImportError'.$randomNumber.'.xlsx','UserExportData','completed',$request->all());
                return response()->json([
                    'Status' => 200,
                    'ErrorCount' => $ErrorCount,
                    'Message' => 'User Data Import Error',
                    'TotalCount' => count($import->getImportedData()),
                    'download_link' => Storage::disk('public')->url('Errors/EmployeeImportError'.$randomNumber.'.xlsx'),
                ]);
            }
            return response()->json([
                'Status' => 200,
                'TotalCount' => count($import->getImportedData()),
                'Message' => 'File uploaded successfully',
            ]);
        }
        elseif($request->type == 'P')
        {
            $path = 'Errors/PospImportError'.$randomNumber.'.xlsx';
            if (count($import->getErrors()) > 0) {
                Excel::Store(new UserdataUploadError($import->getErrors()), $path,'public');
                $this->ExcelLog($this->Auth->id,$path,'UserExportData','completed',$request->all());
                return response()->json([
                    'Status' => 200,
                    'Message' => 'User Data Import Error',
                    'ErrorCount' => $ErrorCount,
                    'TotalCount' => count($import->getImportedData()),
                    'download_link' => Storage::disk('public')->url('Errors/PospImportError'.$randomNumber.'.xlsx'),
                ]);
            }
            if(count($mappingsErrros) > 0)
            {
                $path  = 'Errors/PospImportError'.$randomNumber.'.xlsx';
                Excel::Store(new UserdataUploadError($mappingsErrros), 'Errors/PospImportError'.$randomNumber.'.xlsx','public');
                $this->ExcelLog($this->Auth->id,$path,'UserExportData','completed',$request->all());
                return response()->json([
                    'Status' => 200,
                    'Message' => 'User Data Import Error',
                    'ErrorCount' => $ErrorCount,
                    'TotalCount' => count($import->getImportedData()),
                    'download_link' => Storage::disk('public')->url('Errors/PospImportError'.$randomNumber.'.xlsx'),
                ]);
            }

            return response()->json([
                'Status' => 200,
                'TotalCount' => count($import->getImportedData()),
                'Message' => 'File uploaded successfully',
            ]);
        }
        elseif($request->type == 'Partner'){
            $path = 'Errors/PartnerImportError'.$randomNumber.'.xlsx';
            if (count($import->getErrors()) > 0) {
                Excel::Store(new UserdataUploadError($import->getErrors()), $path,'public');
                $this->ExcelLog($this->Auth->id,$path,'UserExportData','completed',$request->all());
                return response()->json([
                   'Status' => 200,
                    'Message' => 'User Data Import Error',
                    'ErrorCount' => $ErrorCount,
                    'TotalCount' => count($import->getImportedData()),
                    'download_link' => Storage::disk('public')->url('Errors/PartnerImportError'.$randomNumber.'.xlsx'),
                ]);
            }
            if(count($mappingsErrros) > 0)
            {
                Excel::Store(new UserdataUploadError($mappingsErrros), 'Errors/PartnerImportError'.$randomNumber.'.xlsx','public');
                $this->ExcelLog($this->Auth->id,'Errors/PartnerImportError'.$randomNumber.'.xlsx','UserExportData','completed',$request->all());
                return response()->json([
                    'Status' => 200,
                    'ErrorCount' => $ErrorCount,
                    'Message' => 'User Data Import Error',
                    'TotalCount' => count($import->getImportedData()),
                    'download_link' => Storage::disk('public')->url('Errors/PartnerImportError'.$randomNumber.'.xlsx'),
                ]);
            }
            return response()->json([
                'Status' => 200,
                'TotalCount' => count($import->getImportedData()),
                'Message' => 'File uploaded successfully',
            ]);
        }
    }
    public function DownloadExcelTemplate(Request $request)
    {
        $permission = credential_decrypt(config('Permission.user.upload'));
        if (!$this->Auth->can($permission)) {
            return requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $validate = $request->validate([
            'type' => ['required',"in:E,P,Partner"],
        ]);
        $fileUrl = null;
        if($request->type == 'E')
        {
            $excelFileName = 'employeeDataupload.xlsx';
            $fileUrl = Storage::disk('public')->url($excelFileName);
            $this->ExcelLog($this->Auth->id,$excelFileName,'UserExportTemplateDownload','completed',$request->all());

        }
        else if($request->type == 'P')
        {
            $excelFileName = 'POSDataUploadNew.xlsx';
            $fileUrl = Storage::disk('public')->url($excelFileName);
            $this->ExcelLog($this->Auth->id,$excelFileName,'UserExportTemplateDownload','completed',$request->all());

        }else if($request->type == 'Partner'){
            $excelFileName = 'PartnerDataupload.xlsx';
            $fileUrl = Storage::disk('public')->url($excelFileName);
            $this->ExcelLog($this->Auth->id,$excelFileName,'UserExportTemplateDownload','completed',$request->all());
        }
        return [
            'data' => [
            'status' => 'success',
            'message' => 'File is ready for download.',
            'download_link' => $fileUrl,

            ]
        ];
    }
    public function getImportedData()
    {
        return $this->importedData;
    }
    public function ExcelLog($userId, $path,$source,$status,$request)
    {
        DataExportLog::create([
            'user_id' => $userId,
            'file' => $path,
            'source' => $source,
            'status' => $status,
            'request' => json_encode($request),
            'created_at' => now(),
            'file_expiry' => now()->addDays(1),
            'uid' => getUUID()
        ]);
    }
}
