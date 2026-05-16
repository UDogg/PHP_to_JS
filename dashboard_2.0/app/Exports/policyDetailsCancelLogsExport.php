<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class policyDetailsCancelLogsExport implements FromCollection,WithHeadings
{
    
    protected $data;

    public function __construct($data)
    {
        
        $this->data = $data;
    }

    public function collection()
    {
        return collect($this->data)->map(function ($item) {
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
