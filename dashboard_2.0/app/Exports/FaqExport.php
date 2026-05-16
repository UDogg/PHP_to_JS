<?php

namespace App\Exports;

use App\Models\Faq;
use Maatwebsite\Excel\Concerns\FromCollection;
use Illuminate\Support\Collection;
use Maatwebsite\Excel\Concerns\FromArray;
use Maatwebsite\Excel\Concerns\WithHeadings;



class FaqExport implements FromArray, WithHeadings
{
    /**
    * @return \Illuminate\Support\Collection
    */

    protected $headings;

    public function __construct()
    {
        $this->headings = $this->extractHeadings();
    }

    public function array(): array
    {
        return [];
    }

    public function headings(): array
    {
        return $this->headings;
    }

    protected function extractHeadings(): array
    {
        return [
            'Question',
            'Answer',
        ];
    }
}
