<?php

namespace App\Exports;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;
class PospExcelFile implements FromCollection, WithHeadings
{

    public function collection()
    {
        return collect([]); // Return an empty collection
    }

    public function headings(): array
    {
        return ['POS User Name',
        'Name',
        'Middle Name',
        'Last Name',
        'Gender',
        'DOB',
        'Address',
        'Pincode',
        'Mobile Number',
        'Email Address',
        'Qualification',
        'POS Code',
        'Aadhar No',
        'PanCard No',
        'License Start Date',
        'License End Date',
        'Bank Account Holder Name',
        'Bank Account Number',
        'Bank IFSC Code',
        'Bank Name',
        'Bank City Name',
        'Branch Name',
        'Role',
        'Zone',
        'Lob',
        'Reporting Role',
        'Reporting username'];
    }
}
