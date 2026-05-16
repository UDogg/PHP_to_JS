<?php

namespace App\Exports;

use App\Models\User;
use Illuminate\Support\Facades\Auth;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class UserDataExport implements FromCollection, WithHeadings
{
    /**
     * @return \Illuminate\Support\Collection
     */
    private $request;

    private $finalMappingData;

    public function __construct($request, $finalMappingData)
    {
        $this->request = $request;
        $this->finalMappingData = $finalMappingData;

    }

    public function collection()
    {

        $users = User::select('id', 'name', 'middle_name', 'last_name', 'email', 'dob', 'mobile', 'address', 'pincode', 'adhar_no', 'pan_no', 'employee_code', 'usertype', 'created_at', 'reportingto')->with(['roles', 'reportingToUser.roles']);

        $user = Auth::user();
        $userId = $user['id'] ?? '';

        $userType = $user['usertype'] ?? '';

        $users = $users->where('users.username', '!=', credential_encrypt('super_admin'));
        $users = $users->where('users.usertype', '!=', 5);
        if (! empty($this->request->usertype)) {
            $users = $users->where('usertype', $this->request->usertype);
        }

        $finalMappingData = $this->finalMappingData;
        if (empty($finalMappingData)) {
            if ($user->is_admin != 'Y' || $user->usertype != 1) {
                $employeeData = getUserLowerHierarchyWithMapping($userId, $userType);
                // $employeeIds = array_map(function ($user) {
                //     return $user['id'];
                // }, $employeeData);

                $users = $users->whereIn('users.id', $employeeData);
            }
        } else {
            $users = $users->whereIn('users.id', $finalMappingData);
        }

        $users = $users->get();

        $userTypeMapping = [
            1 => 'Employee',
            2 => 'POS',
            3 => 'Partner',
            4 => 'B2C',
            5 => 'Customer',
        ];

        $usersData = $users->map(function ($user) use ($userTypeMapping) {

            $reportingToName = null;
            $reportingToRole = null;

            if ($user->reportingToUser) {
                $reportingToName = credential_decrypt($user->reportingToUser->name);
                $reportingToRole = $user->reportingToUser->getRoleNames()->first() ?? 'No Role Assigned';
            }

            return [
                'name' => credential_decrypt($user->name),
                'middle_name' => credential_decrypt($user->middle_name),
                'last_name' => credential_decrypt($user->last_name),
                'email' => credential_decrypt($user->email),
                'dob' => credential_decrypt($user->dob),
                'mobile' => credential_decrypt($user->mobile),
                'address' => credential_decrypt($user->address),
                'pincode' => credential_decrypt($user->pincode),
                'adhar_no' => credential_decrypt($user->adhar_no),
                'pan_no' => credential_decrypt($user->pan_no),
                'role' => $user->getRoleNames()->first() ?? 'No Role Assigned',
                'usertype' => $userTypeMapping[$user->usertype] ?? 'Unknown',
                'reportingto' => $reportingToName,
                'reportingto_role' => $reportingToRole,
                'employee_code' => credential_decrypt($user->employee_code),
                'created_at' => $user->created_at ?? null,
            ];
        });

        return $usersData;
    }

    public function headings(): array
    {
        return [
            'Name',
            'Middle Name',
            'Last Name',
            'Email',
            'Dob',
            'Mobile',
            'Address',
            'Pincode',
            'Adhar No',
            'Pan No',
            'Role',
            'User Type',
            'ReportingTo',
            'ReportingToRole',
            'Employee Code',
            'Created At',
        ];
    }
}
