<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class OfflinePolicySampleExport implements FromCollection, WithHeadings
{
    protected $headers;
    protected $sampleData;

    public function __construct($columnData)
    {
        $this->headers = array_keys($columnData);
        $this->sampleData = array_values($columnData);
    }

    public function collection()
    {
        // Return empty collection or dummy data
        return collect([$this->sampleData]);
    }

    public function headings(): array
    {
        return $this->headers;
    }
}
