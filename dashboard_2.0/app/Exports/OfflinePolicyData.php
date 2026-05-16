<?php

namespace App\Exports;

use Illuminate\Support\Collection;
use Maatwebsite\Excel\Concerns\WithMapping;
use Maatwebsite\Excel\Concerns\WithHeadings;
use Maatwebsite\Excel\Concerns\FromCollection;

class OfflinePolicyData implements FromCollection, WithHeadings, WithMapping
{
    protected $data;
    protected $dynamicKeys;

    public function __construct($data)
    {
        $this->data = $data;

        $this->dynamicKeys = collect($data)
            ->flatMap(function ($policy) {
                return array_keys((array) ($policy->data ?? []));
            })
            ->unique()
            ->sort()
            ->values()
            ->toArray();
    }

    public function collection(): Collection
    {
        return collect($this->data);
    }

    public function headings(): array
    {
        return array_merge(
            $this->dynamicKeys,
            ['created_at', 'updated_at']
        );
    }

    public function map($policy): array
    {
        $data = (array) ($policy->data ?? []);

        $row = collect($this->dynamicKeys)->map(function ($key) use ($data) {
            return $data[$key] ?? '';
        })->toArray();

        return array_merge($row, [
            $policy->created_at,
            $policy->updated_at,
        ]);
    }
}
