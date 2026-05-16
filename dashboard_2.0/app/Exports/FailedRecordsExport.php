<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;
use Illuminate\Support\Collection;

class FailedRecordsExport implements FromCollection, WithHeadings
{
    protected $failedRecords;

    public function __construct(array $failedRecords)
    {
        $this->failedRecords = $failedRecords;
    }

    public function collection()
    {
        return new Collection(array_map(function ($record) {
            return [
                'User Code' => $record['mobile'],
                'Name' => $record['label'],
                'Error Reason' => $record['error_reason'] ?? 'Unknown Error'
            ];
        }, $this->failedRecords));
    }

    public function headings(): array
    {
        return ["User Code", "Name", "Error Reason"];
    }
    
}