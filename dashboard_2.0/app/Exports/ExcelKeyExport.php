<?php

namespace App\Exports;

use App\Models\ExcelKeyMaster;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class ExcelKeyExport implements FromCollection, WithHeadings
{
    protected $lob_id;
    protected $errorMessages;

    public function __construct($lob_id,$errorMessages = [])
    {
        $this->lob_id = $lob_id;
        $this->errorMessages = $errorMessages;
       
    }
    public function collection()
    {
       
        $errorRow = collect([$this->errorMessages]);
        $getData = ExcelKeyMaster::get()->where('lob_id', $this->lob_id)->where('is_visible', 'Y')->sortBy('sequence');
        $formattedData = $getData->map(function ($item) {
            $dataRow = [];
            $columnNames = json_decode($item->excel_column_name, true);

            if (is_string($columnNames)) {
                $columnNames = [$columnNames];
            }

            if (is_array($columnNames)) {
                foreach ($columnNames as $columnName) {
                    $dataRow[$columnName] = $item->$columnName;
                }
            }

            return $dataRow;
        });
        return $errorRow->concat($formattedData);
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
        $headings[] = 'Error Message';
        
        return $headings;
    }
}
