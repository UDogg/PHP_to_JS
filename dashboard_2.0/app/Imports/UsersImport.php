<?php

namespace App\Imports;

use Maatwebsite\Excel\Concerns\ToCollection;
use Illuminate\Support\Collection;

class UsersImport implements ToCollection
{
    public $data;

    public function collection(Collection $rows)
    {
        $this->data = $rows->map(function ($row) {
            return [
                "Username" => $row[0],
                "POS_Code" => $row[1],
            ];
        });
    }

    public function getData()
    {
        return $this->data;
    }
}
