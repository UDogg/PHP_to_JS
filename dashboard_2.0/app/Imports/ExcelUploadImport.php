<?php

namespace App\Imports;

use App\Models\ExcelKeyMaster;
use Illuminate\Support\Collection;
use Maatwebsite\Excel\Concerns\ToCollection;

class ExcelUploadImport implements ToCollection
{
    /**
    * @param Collection $collection
    */
    public $data;
    protected $lob_id;
    private $columns;
    public function __construct($lob_id)
    {
        $this->lob_id = $lob_id;
        $this->columns = ExcelKeyMaster::where('lob_id', $lob_id)
            ->where('is_visible', 'Y')
            ->pluck('excel_column_name')
            ->toArray();
    }
    
    public function collection(Collection $rows)
    {
        $rows = $rows->values();

        $headerRow = $rows->first()->toArray();

        $validIndexes = [];
        $filteredHeaders = [];

        foreach ($headerRow as $index => $header) {
            if (!is_null($header) && trim($header) !== '') {
                $validIndexes[] = $index;
                $filteredHeaders[] = $header;
            }
        }

        $this->data = $rows->slice(1)->map(function ($row) use ($validIndexes, $filteredHeaders) {
            $rowData = $row->toArray();

            $filteredRowData = [];
            foreach ($validIndexes as $index) {
                $filteredRowData[] = $rowData[$index] ?? null;
            }

            return array_combine($filteredHeaders, $filteredRowData);
        });
    }

    public function chunkSize(): int
    {
        return 500;
    }

    public function getData()
    {
        return $this->data;
    }
}
