<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromArray;
use Maatwebsite\Excel\Concerns\WithHeadings;

class CrossSellListDataExport implements FromArray, WithHeadings
{
    protected $data;
    protected $headings;

    /**
     * Constructor to receive the data and headings
     *
     * @param array $data
     * @param array $headings
     */
    public function __construct(array $data, array $headings)
    {
        $this->data = $data;
        $this->headings = $headings;
    }

    /**
     * Return the data to be exported
     *
     * @return array
     */
    public function array(): array
    {
        return $this->data;
    }

    /**
     * Return the headings for the Excel sheet
     *
     * @return array
     */
    public function headings(): array
    {
        return $this->headings;
    }
}
