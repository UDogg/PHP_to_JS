<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;
use Illuminate\Support\Collection;


class VisibilityReportExport implements FromCollection, WithHeadings
{
    protected $headings;
    protected $data = [];

    public function __construct(array $data)
    {
        $this->data = $data;
        $this->headings = $this->extractHeadings();

    }

    public function collection()
    {
        $mongoData = $this->data;
        return  new Collection($mongoData);
    }
    public function headings(): array
    {
        return $this->headings;
    }

    protected function extractHeadings(): array
    {
        
        $documents = $this->data;
        $headings = [];
        foreach ($documents as $document) {
            $headings = array_merge($headings, array_keys(iterator_to_array($document)));
        }
        return array_unique($headings);
    }
    
}
