<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromArray;
use Maatwebsite\Excel\Concerns\WithHeadings;

class VisibilitySuccessFailureReportExport implements FromArray, WithHeadings
{
    protected $exportData;
    protected $headings;

    public function __construct(array $exportData, array $headings)
    {
        $this->exportData = $exportData;
        $this->headings = $headings;
    }

    public function array(): array
    {
        return $this->exportData;
    }

    public function headings(): array
    {
        return $this->headings;
    }
}
