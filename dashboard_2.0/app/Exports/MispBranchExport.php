<?php

namespace App\Exports;

use App\Models\MispBranch;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;


class MispBranchExport implements FromCollection, WithHeadings
{
    /**
    * @return \Illuminate\Support\Collection
    */
    protected $headings;
    protected $data = [];
    protected $misp_branch = [];
    public function __construct($misp_branch)
    {
        $this->misp_branch = $misp_branch;
    }
    public function collection()
    {
        return collect($this->misp_branch);
    }
    public function headings(): array
    {
        // return $this->headings;
        return [
            'Branch ID',
            'Oem Id',
            'oem_name',
            'misp_id',
            'misp_name',
            'branch_name',
            'address',
            'city',
            'state',
            'pin_code',
            'code',
            'created_at',
            'updated_at',
            'deleted_at',
            'zone',
            'mobile_number',
            'email',
            'status',


            // Add any other relevant column headings
        ];
    }
    protected function extractHeadings(): array
    {

        $documents = $this->misp_branch;
        $headings = [];
        foreach ($documents as $document) {
            $headings = array_merge($headings, array_keys(iterator_to_array($document)));
        }
        return array_unique($headings);
    }
}
