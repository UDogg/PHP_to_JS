<?php

namespace App\Imports;

use Illuminate\Support\Collection;
use Maatwebsite\Excel\Concerns\ToCollection;

class EmailWhitelistingImport implements ToCollection
{
    public $data;
    /**
    * @param Collection $collection
    */
    public function collection(Collection $rows)
    {
        $this->data = $rows->map(function ($row) {
            return [
                "Email_id" => $row[0],
                "Mobile_No" => $row[1],
                "Status" => $row[2],
            ];
        });
    }
    public function getData()
    {
        return $this->data;
    }
}
