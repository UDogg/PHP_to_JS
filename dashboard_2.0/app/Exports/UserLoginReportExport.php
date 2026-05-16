<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromArray;
use Maatwebsite\Excel\Concerns\WithHeadings;

class UserLoginReportExport implements FromArray, WithHeadings
{
    protected $data;

    public function __construct(array $data)
    {
        // Remove 'id' from each row
        $this->data = array_map(function ($row) {
            unset($row['id']);
            return $row;
        }, $data);
    }

    public function array(): array
    {
        return $this->data;
    }

    public function headings(): array
    {
        return [
            'SR NO',
            // 'id',
            'name',
            'Role',
            'Lob',
            'Last Login Date',
            'Login Count',
        ];
    }
}
