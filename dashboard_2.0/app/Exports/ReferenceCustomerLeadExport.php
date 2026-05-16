<?php
namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Illuminate\Support\Collection;

class ReferenceCustomerLeadExport implements FromCollection
{
    public $data;

    public function __construct($data)
    {
        $this->data = $data;
    }

    public function collection()
    {
        $exportData = collect([
            ['Name', 'Email', 'Mobile','Created By'],
        ]);

        foreach ($this->data as $item) {
            $exportData->push([
                $item->name,
                $item->email,
                $item->mobile,
                $item->created_by,
            ]);
        }

        return $exportData;
    }
}
