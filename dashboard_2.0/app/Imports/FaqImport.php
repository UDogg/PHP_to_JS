<?php

namespace App\Imports;

use App\Models\Faq;
use Maatwebsite\Excel\Concerns\ToModel;
use Maatwebsite\Excel\Concerns\WithHeadingRow;


class FaqImport implements ToModel, WithHeadingRow
{
    /**
    * @param array $row
    *
    * @return \Illuminate\Database\Eloquent\Model|null
    */
    protected $tag_id;

    public function __construct($tag_id)
    {
        $this->tag_id = $tag_id;
    }
    public function model(array $row)
    {
        if (isset($row['question']) && isset($row['answer'])) {
            return new Faq([
                'tag' => $this->tag_id,
                'question' => $row['question'],
                'answer' => $row['answer'],
            ]);
        }
        return null;
    }
}
