<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class EmpployeeExcelFile implements FromCollection, WithHeadings
{
    public function collection()
    {
        return collect([]); // Return an empty collection
    }

    public function headings(): array
    {
        return ['User Name','Name','Middle Name','Last Name','Gender','DOB','Address','Pincode','Mobile Number','Email Address','Qualification','Employee Code','Aadhar no','PanCard No','Bank Account Holder Name','Bank Account Number','Bank IFSC Code','Bank Name','Bank City Name','Bank Branch','Role','Zone','Lob','Reporting Role','Reporting Username','Password'];
    }
}
