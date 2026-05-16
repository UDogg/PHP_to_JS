<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class IssuedPolicyExport implements FromCollection,WithHeadings
{
    /**
    * @return \Illuminate\Support\Collection
    */
    protected $data;

    public function __construct($data)
    {
        $this->data = $data;
    }

    public function collection()
    {
        return $this->data;
    }

    public function headings(): array
    {
        return [
            'ID',
            'Trace ID',
            'Policy No',
            'Proposer Name',
            'Proposer Mobile',
            'Proposer Email ID',
            'Section',
            'Seller Type',
            'Entry Type',
            'Created At',
        ];
    }
}
