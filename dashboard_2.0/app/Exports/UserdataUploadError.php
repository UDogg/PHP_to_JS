<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromArray;
use Maatwebsite\Excel\Concerns\WithHeadings;

class UserdataUploadError implements FromArray, WithHeadings
{
    protected $errors;

    public function __construct(array $errors)
    {
        $this->errors = $errors; // each item = ['row' => [...], 'errors' => [...]]
    }

    public function headings(): array
    {
        if (empty($this->errors)) {
            return [];
        }

        $firstRow = $this->errors[0]['row'];
        $headings = array_keys($firstRow);
        $headings[] = 'Errors'; // add final error column
        return $headings;
    }

    public function array(): array
    {
        $output = [];

        foreach ($this->errors as $entry) {
            $rowData = $entry['row'];
            $errorMessages = is_array($entry['errors']) ? implode(', ', $entry['errors']) : $entry['errors']; // convert array to string
            $rowData['Errors'] = $errorMessages;

            $output[] = $rowData;
        }

        return $output;
    }
}
