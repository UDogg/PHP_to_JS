<?php

namespace App\Exports;

use Generator;
use Maatwebsite\Excel\Concerns\FromGenerator;
use Maatwebsite\Excel\Concerns\WithHeadings;

class ReportExport implements FromGenerator, WithHeadings
{
    protected $cursor;
    protected $headings;

    public function __construct($cursor)
    {
        $this->cursor = $cursor;
        $this->headings = $this->extractHeadings();
    }

    public function generator(): Generator
    {
        foreach ($this->cursor as $document) {
            yield $this->flattenDocument($document);
        }
    }

    public function headings(): array
    {
        return $this->headings;
    }

    protected function extractHeadings(): array
    {
        foreach ($this->cursor as $document) {
            return array_keys($this->flattenDocument($document));
        }
        return [];
    }

    protected function flattenDocument($document): array
    {
        return iterator_to_array($document);
    }
}
