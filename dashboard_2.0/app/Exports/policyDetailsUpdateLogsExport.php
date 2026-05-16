<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class policyDetailsUpdateLogsExport implements FromCollection,WithHeadings
{
    protected $data;

    public function __construct($data)
    {
        // Assuming $data is already a Laravel Collection
        $this->data = $data;
    }

    public function collection()
    {
        // No need to use collect() since $this->data is already a Collection
         // Remove 'screenshot' from each row before returning
         return $this->data->map(function ($item) {
            unset($item['screenshot']); 
            unset($item['old_data']); 
            unset($item['new_data']); 

            return $item;
        });
    }

    public function headings(): array
    {
        return [
            'Sr No',
            'Trace ID',
            'Policy No',
            'Section',
            'Policy Type',
            'Action Type',
            'Update Timestamp',
            // 'Screenshot'
        ];
    }
}
