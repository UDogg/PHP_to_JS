<?php

namespace App\Exports;

use App\Models\ExcelKeyMaster;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class ExcelKeyMasterExport implements FromCollection, WithHeadings
{
    protected $lob_id;

    public function __construct($lob_id)
    {
        $this->lob_id = $lob_id;
    }
    public function collection()
    {
        $getData = ExcelKeyMaster::get()->where('lob_id', $this->lob_id)->where('is_visible', 'Y')->sortBy('sequence');
        return $getData->map(function ($item) {
            $formattedData = [];
            $columnNames = json_decode($item->excel_column_name, true);
            if (is_string($columnNames)) {
                $columnNames = [$columnNames];
            }
            if (is_array($columnNames)) {
                foreach ($columnNames as $columnName) {
                    $formattedData[$columnName] = $item->$columnName;
                }
            }

            return $formattedData;
        });
    }

    public function headings(): array
    {
        $headings = [];
        $firstItem = ExcelKeyMaster::where('lob_id', $this->lob_id)
        ->where('is_visible', 'Y')
        ->select('excel_column_name', 'sequence')
        ->orderBy('sequence')
        ->get();
        if ($firstItem) {
            $sortedItems = $firstItem->sortBy('sequence'); 
            foreach ($sortedItems as $columnName) {
                $headings[] = $columnName['excel_column_name'];
            }
        }
        return $headings;
    }
}
