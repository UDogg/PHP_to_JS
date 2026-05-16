<?php

namespace App\Http\Controllers;

use App\Models\User;
use App\Models\userTypes;
use Illuminate\Support\Str;
use MongoDB\Operation\Find;
use Illuminate\Http\Request;
use App\Exports\AllDataExport;
use App\Jobs\ExportLargeExcel;
use Illuminate\Support\Carbon;
use App\Models\ExcelDownloadLog;
use Spatie\Permission\Models\Role;
use App\Models\delegateMasterModel;
use Illuminate\Support\Facades\Auth;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;
use Illuminate\Pagination\LengthAwarePaginator;

class DelegateMasterController extends Controller
{
    public $AuthUser;
    public function __construct(Auth $auth)
    {
        $this->AuthUser = $auth::user();
    }
    public function AllowUsers(Request $request)
    {
        $usersList  = $request->usersId;
        $getUsertype = userTypes::select('id')->where('Identifier','E')->first()['id'];
        $checkIfUsersAreEmployees = User::select('username','id','usertype')->whereIn('id', $usersList)->get();
        foreach($checkIfUsersAreEmployees as $checkIfUsersAreEmployee)
        {
            if($checkIfUsersAreEmployee->usertype != $getUsertype && in_array($checkIfUsersAreEmployee->id, $usersList))
            {
                return requestResponseMessage(['status' => 500, 'message' => 'This Users Is Not Emplyee Usertype !'.credential_decrypt($checkIfUsersAreEmployee->username)]);
            }
            if(!in_array($checkIfUsersAreEmployee->id, $usersList))
            {
                return requestResponseMessage(['status' => 500, 'message' => 'This Users Is Not In The List !'.credential_decrypt($checkIfUsersAreEmployee->username)]);
            }
        }
        $allowedDelegateCount = $request->count;
        $users = User::WhereIn('id', $usersList)->update([
            'is_delegate'=>'Y',
            'delegate_count' => $allowedDelegateCount
        ]);
        if($users)
        {
            return response()->json(['status' => "true",'message' => "Allowed To Create Delegate Users Successfully"]);
        }
        else
        {
            return response()->json(['status' => "false",'message' => "Something went wrong"]);
        }

    }
    public function MapUsers(Request $request)
    {
        $Permission = credential_decrypt(config('Permission.delegate.edit'));
        if (!$this->AuthUser->can($Permission)) {
            return  requestResponseMessage(['status' => 404, 'message' => 'Access Denied']);
        }
        $validate  = $request->validate([
            'delegateUserId' => 'required',
            'is_active' => 'required|in:Y,N',
        ]);
        $userId  =$this->AuthUser->id;
        $delegateUserId = $request->delegateUserId;
        $is_active = $request->is_active;
        $user = User::where('id',$userId)->where('Is_delegate','Y')->first();
        if(empty($user))
        {
            return requestResponseMessage(['status' => 500, 'message' => 'User Is Not allowed To Create Delegate Users']);
        }
        $count = delegateMasterModel::where('user_id',$this->AuthUser->id)->count();
        $allowedCount = User::where('id',$userId)->select('delegate_count')->first()['delegate_count'];
        if($count >= $allowedCount)
        {
            return requestResponseMessage(['status' => 500, 'message' => 'No More Delegate Creation Allowed']);
        }
        foreach($delegateUserId as $duserId)
        {
            $check = delegateMasterModel::where('user_id',$userId)->where('delegate_user_id',$duserId)->first();
            if($check)
            {
                continue;
            }
            else
            {
                $mapuser  = delegateMasterModel::insert([
                    'user_id' => $userId,
                    'delegate_user_id' => $duserId,
                    'is_active'=> $is_active,
                    'created_at' => date('Y-m-d H:i:s'),
                ]);
            }

        }
        if($mapuser)
        {
            return response()->json(['status' => "true",'message' => "Delegate User Assigned Successfully"]);
        }
        else
        {
            return response()->json(['status' => "false",'message' => "Something went wrong"]);
        }

    }
    public function SwitchDelegate(Request $request)
    {
        $validate  = $request->validate([
            'userId' => 'required',
            'delegateUserId' => 'required',
        ]);
        $checkDelegateMapping = delegateMasterModel::where('user_id',$request->userId)->where('delegate_user_id',$request->delegateUserId)->first();
        if(empty($checkDelegateMapping))
        {
            return requestResponseMessage(['status' => 500,'message' => 'delegate not present']);
        }
        $prevUserdata = User::where('id',$request->delegateUserId)->first();
        $finalPrevData = [];
        // foreach ($prevUserdata as $predate)
        // {

            $finalPrevData[] = [
                'previousUserId'=> $prevUserdata->id,
                'name' => credential_decrypt($prevUserdata->name),
                'email' => credential_decrypt($prevUserdata->email),
                'username' => credential_decrypt($prevUserdata->username),
                'mobile' => credential_decrypt($prevUserdata->mobile),
                'address' => credential_decrypt($prevUserdata->address),
                'gender' => $prevUserdata->gender,
            ];

        // }
        $user = User::find($request->userId);
        if($user && $user->Is_delegate == 'Y')
        {
            $delegateUserId = $prevUserdata->id; 
            $username = credential_decrypt($prevUserdata->username);
            $tokenAbilities = [
                "delegate" => [
                    "delegate_user_id" => $delegateUserId,
                    "delegate_username" => $username,
                ]
            ];
            $token = generateTokenAll($user,$tokenAbilities);

            return requestResponseMessage(['status' => 200,'message' => 'Logged In As Delegate User','data' => [
                'token' => $token,
                'prevUserdata' => $finalPrevData]]);

        }
        else
        {
            return requestResponseMessage(['status' => 500,'message' => 'User Not Found']);
        }
    }
    public function RevertToPreviousLogin(Request $request)
    {
        $validate = $request->validate([
            'currentUserId' => 'required',
            'previousUserId' => 'required',
        ]);

        $checkDelegateMapping = delegateMasterModel::where('user_id', $request->currentUserId)
            ->where('delegate_user_id', $request->previousUserId)
            ->first();

        if (empty($checkDelegateMapping)) {
            return requestResponseMessage([
                'status' => 500,
                'message' => 'Mapping not found for the previous login'
            ]);
        }

        $prevUser = User::find($request->previousUserId);
        $user = User::find($request->currentUserId);
        if($user && $user->Is_delegate == 'Y')
        {
            $token = generateTokenAll($prevUser);

            return requestResponseMessage([
                'status' => 200,
                'message' => 'Reverted back to previous login successfully',
                'data' => [
                    'token' => $token,
                ]
            ]);
        }
        else
        {
            return requestResponseMessage(['status' => 500,'message' => 'User Not Found']);
        }
        
    }

    public function getDelegateUsers(Request $request)
    {
        $validate = $request->validate([

            'userId' => 'required',
        ]);
        $delegateCount  = User::where('id',$request->userId)->select('delegate_count')->first()['delegate_count'];
        $getUsers = delegateMasterModel::select('delegate_master.user_id as id','delegate_master.delegate_user_id','users.username')->where('user_id',$request->userId)->join('users','users.id','delegate_master.delegate_user_id')->get()->toArray();

        foreach($getUsers as $key => $value)
        {
            $getUsers[$key]['username'] = credential_decrypt($value['username']);
        }

        if($getUsers)
        {
            return response()->json(['status' => 200,'message' => 'User Found','data' => $getUsers,'MaxDelegateCount' => $delegateCount ]);
        }
        else
        {
            return requestResponseMessage(['status' => 500,'message' => 'User Not Found']);
        }

    }
    
    public function DelegateDetails(Request $request)
    {
        $request->validate([
            'page' => 'integer',
            'perPageRecords' => 'integer',
            'pagination' => 'boolean',
            'export' => 'boolean',
            'search' => 'nullable|string',
        ]);

        $pagination = $request->input('pagination', true);
        $page = $request->input('page', 1);
        $perPageRecords = $request->input('perPageRecords', 10);
        $search = $request->input('search', '');

        $detailsArr = [];
        $isAdmin = UserIsAdmin($this->AuthUser->id);

        $usersdata = User::select('username', 'delegate_count', 'id')
            ->where('Is_delegate', 'Y');

        if (!$isAdmin) {
            $usersdata = $usersdata->where('id', $this->AuthUser->id);
        }

        if (!empty($search)) {
            $usersdata->where('username', 'LIKE', "%{$search}%");
        }

        if ($pagination) {
            $usersdataPaginated = $usersdata->paginate($perPageRecords, ['*'], 'page', $page);
            $lastPage = $usersdataPaginated->lastPage();
            $totalCount = $usersdataPaginated->total();
            $prevPage = $usersdataPaginated->previousPageUrl() ? $page - 1 : null;
            $nextPage = $usersdataPaginated->nextPageUrl() ? $page + 1 : null;
            $usersdata = $usersdataPaginated->items();
        } else {
            $usersdata = $usersdata->get();
            $totalCount = $usersdata->count();
        }
//use whereIn for getting user details 
        foreach ($usersdata as $u) {
            $delegateuserDetails = delegateMasterModel::select(
                'delegate_master.delegate_user_id',
                'users.username',
                'delegate_master.id',
                'delegate_master.user_id',
                'users.delegate_count'
            )
            ->where('user_id', $u['id'])
            ->where('delegate_master.is_active', 'Y')
            ->join('users', 'users.id', 'delegate_master.delegate_user_id')
            ->get();

            foreach ($delegateuserDetails as $key => $delegatedata) {
                $delegateuserDetails[$key]['username'] = credential_decrypt($delegatedata['username']);
                $delegateuserDetails[$key]['id'] = $delegatedata['id'];
                $delegateuserDetails[$key]['delegate_count'] = $delegatedata['delegate_count'];
            }

            if (!$isAdmin) {
                foreach ($delegateuserDetails as $delegatedata) {
                    $delegateName = $delegatedata['username'];
                    $delegateeId = $delegatedata['delegate_user_id'];
                    $delegateuser = User::select('username')->where('id', $this->AuthUser->id)->first();
                    $delegateusername = credential_decrypt($delegateuser['username']);
                    $userRole = $u->getRoleNames()->implode(',');

                    $detailsArr[] = [
                        'delegateUserId' => $delegatedata['id'],
                        'username' => $delegateusername,
                        'delegateNames' => $delegateName,
                        'delegateeRole' => $userRole,
                        'delegateeId' => $delegateeId,
                    ];
                }
            } else {
                $detailsArr[] = [
                    "userId" => $u['id'],
                    "DelegateMasterId" => $delegateuserDetails->pluck('id')->implode(','),
                    "Username" => credential_decrypt($u['username']),
                    "DelegateUserName" => $delegateuserDetails->pluck('username')->implode(','),
                    "rolename" => $u->getRoleNames(),
                    'delegate_count' => $u['delegate_count'],
                ];
            }
        }

        if ($request->input('export', false)) {
            $dataCount = count($detailsArr);
            $maxAllowedCount = config('excel.data.limit.download');
            $headings = ['Username', 'DelegateUserName', 'rolename', 'delegate_count'];

            if ($dataCount > $maxAllowedCount) {
                ExcelDownloadLog::insert([
                    'user_id' => Auth::id(),
                    'request' => json_encode($request->all()),
                    'status' => '0',
                    'created_at' => Carbon::now(),
                    'source' => 'Delegate Data Export'
                ]);

                $random = rand(1, 10000000);
                $filename = 'Data/Delegate' . $random . '.xlsx';
                ExportLargeExcel::dispatch($detailsArr, $headings, $request->all(), Auth::id(), 'DelegateDataExport', $filename)->onQueue('LargeExcelExports');

                return response()->json([
                    'status' => 200,
                    'message' => 'Data is too large to download. Added to queue; you will get this file later in the job list.',
                ]);
            } else {
                $export = new AllDataExport($detailsArr, $headings, 'DelegateDataExport');
                $random = Str::random(10);
                $filePath = 'Data/Delegate' . $random . '.xlsx';
                Excel::store($export, $filePath, 'public');
                $downloadLink = Storage::disk('public')->url($filePath);

                ExcelDataExportLog(Auth::id(), $filePath, 'Delegate', 'completed', $request->all());

                return response()->json([
                    'status' => 200,
                    'message' => 'Excel file generated successfully',
                    'link' => $downloadLink,
                ]);
            }
        }

        return response()->json([
            'status' => 200,
            'data' => $detailsArr,
            'pagination' => $pagination ? [
                'pagination_type' => 'integrated',
                'per_page' => $perPageRecords,
                'current_page' => $page,
                'prev_page' => $prevPage,
                'next_page' => $nextPage,
                'total' => $totalCount,
                'last_page' => $lastPage,
            ] : null,
        ]);
    }

    public function updateDelegateDetails(Request $request)
    {
        $request->validate([
            'DelegateUserName' => 'required', 
        ]);
    
        $isAdmin = UserIsAdmin($this->AuthUser->id);
        
        $userId = $isAdmin ? $request->user_id : $request->delegateUserId;
        $DelegateUserNameList = explode(',', $request->DelegateUserName);
        $DelegateUserNameList = array_map(function($username) {
            return credential_encrypt(trim($username)); 
        }, $DelegateUserNameList);
    
        $delegateRecord = User::whereIn('username', $DelegateUserNameList)
                            ->where('Is_delegate', 'Y')
                            ->pluck('id');
    
        $allUpdatesSuccessful = true;
    
        if ($delegateRecord->isNotEmpty()) {
            
            foreach ($delegateRecord as $delegateId) {
                if($isAdmin)
                {
                    delegateMasterModel::where('user_id', $userId)->update(['is_active' => 'N']);
                    delegateMasterModel::where('user_id', $userId)->delete();
                }else{
                    delegateMasterModel::where('id', $userId)->update(['is_active' => 'N']);
                    delegateMasterModel::where('id', $userId)->delete();
                }
                $domainUpdate = delegateMasterModel::create([
                    'user_id' => $this->AuthUser->id,
                    'delegate_user_id' => $delegateId,
                    'is_active' => !empty($delegateId) ? 'Y' : 'N',
                ]);
    
                if (!$domainUpdate) {
                    $allUpdatesSuccessful = false;
                    break;
                }
            }
        }
    
        if ($allUpdatesSuccessful) {
            return requestResponseMessage(['status' => 200, 'message' => 'Data Updated Successfully']);
        } else {
            return requestResponseMessage(['status' => 500, 'message' => 'Something went wrong']);
        }
        
    }

    public function delete(Request $request)
    {
        $isAdmin = UserIsAdmin($this->AuthUser->id);
        $userId = $request->user_id;
        $delegateUserId = $request->delegateUserId;
        $query = delegateMasterModel::query();
        $rowsAffected = 0;
        if ($isAdmin) {
            $rowsAffected  =  User::where('id', $userId)->update(['Is_delegate' => 'N']);
            $rows  = $query->where('user_id', $userId)->delete();
        } else {
            $rowsAffected  = $query->where('id', $delegateUserId)->delete(); 
        }

        if ($rowsAffected > 0) {
            return requestResponseMessage(['status' => 200, 'message' => 'Deleted Successfully']);
        } else {
            return requestResponseMessage(['status' => 500, 'message' => 'No rows affected.']);
        }
       
    }
    
    public function getDelegateLogs(Request $request)
    {
        $request->validate([
            'page' => 'integer',
            'perPageRecords' => 'integer',
            'search' => 'nullable|string',
            'export' => 'boolean',
        ]);

        $page = $request->input('page', 1);
        $perPageRecords = $request->input('perPageRecords', 10);
        $search = $request->input('search', '');

        $isAdmin = UserIsAdmin($this->AuthUser->id);

        $query = delegateMasterModel::withTrashed()
            ->select('delegate_master.user_id', 'delegate_master.delegate_user_id', 'delegate_master.created_at', 'delegate_master.deleted_at', 'u1.username as user_name', 'u2.username as delegate_user_name')
            ->join('users as u1', 'u1.id', '=', 'delegate_master.user_id') // Join to get the username for user_id
            ->join('users as u2', 'u2.id', '=', 'delegate_master.delegate_user_id'); // Join to get the username for delegate_user_id

        if (!empty($search)) {
            $query->where(function ($q) use ($search) {
                $q->where('u1.username', 'LIKE', "%{$search}%")
                ->orWhere('u2.username', 'LIKE', "%{$search}%");
            });
        }

        if (!$isAdmin) {
            $userid = $this->AuthUser->id;
            $query->where('delegate_master.user_id', $userid);
        }

        $delegateAlluserDetails = $query->get();

        $detailsArr = [];
        foreach ($delegateAlluserDetails as $u) {
            $detailsArr[] = [
                'delegateNames' => credential_decrypt($u->delegate_user_name), 
                'delegateeRole' => User::find($u->delegate_user_id)->getRoleNames()->implode(','), 
                // 'created_at' => \Carbon\Carbon::parse($u['created_at'])->format('Y-m-d, h:i:s'),
                'created_at' => Carbon::parse($u['created_at'], 'UTC')->setTimezone('Asia/Kolkata')->format('Y-m-d H:i:s'),
                // 'deleted_at' => \Carbon\Carbon::parse($u['deleted_at'])->format('Y-m-d, h:i:s'),
                'deleted_at' => Carbon::parse($u['deleted_at'], 'UTC')->setTimezone('Asia/Kolkata')->format('Y-m-d H:i:s'),
            ];
        }

        if ($request->input('export', false)) {
            $dataCount = $query->count();
            $maxAllowedCount = config('excel.data.limit.download');
            $headings = ['S.no', 'Delegatee Name', 'Role', 'Created At', 'Deleted At'];

            if ($dataCount > $maxAllowedCount) {
                $random = rand(1, 10000000);
                $filename = 'Data/DELEGATE_DETAILS_' . $random . '.xlsx';
                ExportLargeExcel::dispatch($detailsArr, $headings, $request->all(), Auth::id(), 'DELEGATE_DETAILS', $filename)->onQueue('LargeExcelExports');
                return response()->json([
                    'status' => 200,
                    'message' => 'Data is too large to download. Added to Queue. You will get the file later in job list.'
                ]);
            } else {
                $export = new AllDataExport($detailsArr, $headings, 'DELEGATE_DETAILS');
                $random = Str::random(10);
                $filePath = 'Data/DELEGATE_DETAILS_' . $random . '.xlsx';
                Excel::store($export, $filePath, 'public');
                $downloadLink = Storage::disk('public')->url($filePath);

                return response()->json([
                    'status' => 200,
                    'message' => 'Excel file generated successfully',
                    'link' => $downloadLink,
                ]);
            }
        }

        if ($request->input('pagination', true)) {
            $currentPage = LengthAwarePaginator::resolveCurrentPage();
            $paginatedData = collect($detailsArr)->slice(($currentPage - 1) * $perPageRecords, $perPageRecords)->values();

            $pagination = new LengthAwarePaginator(
                $paginatedData,
                count($detailsArr), 
                $perPageRecords,    
                $currentPage,      
                ['path' => $request->url(), 'query' => $request->query()]
            );

            return response()->json([
                'status' => 200,
                'data' => $paginatedData, 
                'pagination' => [
                    'pagination_type' => 'integrated',
                    'per_page' => $perPageRecords,
                    'current_page' => $pagination->currentPage(),
                    'prev_page' => $pagination->previousPageUrl() ? $currentPage - 1 : null,
                    'next_page' => $pagination->nextPageUrl() ? $currentPage + 1 : null,
                    'total' => $pagination->total(),
                    'last_page' => $pagination->lastPage(),
                ]
            ]);
        } else {
            return response()->json([
                'status' => 200,
                'message' => 'Delegate Details',
                'data' => $detailsArr,
            ]);
        }
    }

    
}
