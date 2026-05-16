<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithMapping;
use Maatwebsite\Excel\Concerns\WithHeadings;

class RenewalDataExport implements FromCollection, WithMapping, WithHeadings
{
    protected $data;

    public function __construct($data)
    {
        $this->data = $data;
    }

    public function collection()
    {
        // Convert the variable data to a Laravel collection
        return collect($this->data);
    }

    /**
     * Map each row for export.
     *
     * @param mixed $row
     * @return array
     */
    public function map($row): array
    {
        return [
            $row['proposer_name'] ?? '',
            $row['proposer_mobile'] ?? '',
            $row['vehicle_registration_number'] ?? '',
            $row['sum_assured'] ?? '',
            $row['company_name'] ?? '',
            $row['policy_no'] ?? '',
            $row['trace_id'] ?? '',
            $row['seller_name'] ?? '',
            $row['lob'] ?? '',
        ];
    }

    public function headings(): array
    {
        
        return [
            'PROPOSER_NAME',
            'PROPOSER_MOBILE',
            'VEHICLE_REGISTRATION_NUMBER',
            'SUM_ASSURED',
            'COMPANY_NAME',
            'POLICY_NO',
            'TRACE_ID',
            'SELLER_NAME',
            'LOB',


        ];
    }


}


