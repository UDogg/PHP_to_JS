<?php

namespace App\Exports;

use App\Models\MongoModel;
use Illuminate\Support\Collection;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\ToModel;
use Maatwebsite\Excel\Concerns\WithHeadingRow;
use Maatwebsite\Excel\Concerns\WithHeadings;
class UsersExport implements FromCollection, WithHeadings
{
    /**
    * @return \Illuminate\Support\Collection
    */
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