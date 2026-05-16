<?php

namespace App\Services;

use App\Models\User;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use App\Models\UserAccessManagment;




class UserService
{
    public function listRoleService()
    {
        $user = Auth::user();
        $list_flag = $user->list_flag;
        $finalMappingData = [];
        if($list_flag){
            $allowedIdentifier = explode(',',$list_flag);
        }
        $roleId = $user->userRoles->pluck('id');
        $json = UserAccessManagment::whereIn('role_id', $roleId)
            ->value('data');
        $data = json_decode($json, true);
        $identifierData= $data['manage_access'][0]['identifier'] ?? null;
        if($identifierData){
            $allowedIdentifier = $identifierData;
        }
        $mapping = [
            'E' => 1,
            'P' => 2,
            'Partner' => 3,
            'SP' => 7
        ];
        if (!empty($allowedIdentifier)) {
            $mappedIds = array_map(fn($val) => $mapping[$val] ?? null, $allowedIdentifier);
            $mappedIds = array_filter($mappedIds);
            $users = User::whereIn('usertype', $mappedIds)->get(); 
            $array = $users->toArray();                     
            $finalMappingData = array_column($array, 'id');
            return $finalMappingData;
        }else{
            return [];
        }
    }
}
