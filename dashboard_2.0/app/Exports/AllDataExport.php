<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class AllDataExport implements FromCollection, WithHeadings
{
    /**
    * @return \Illuminate\Support\Collection
    */

    private $request;
    private $model;
    private $headings;
    private $querycolumn;

    /**
     * Create a new instance of AllDataExport.
     *
     * @param  \Illuminate\Http\Request $request The request containing filter parameters.
     * @param  string $model The model class to be exported.
     * @param  array $headings The headings for the exported file.
     * @param  array $querycolumn The columns to be used for querying the data.
     * @return void
     */
    public function __construct($request, $model, $headings, $querycolumn)
    {
        $this->request = $request;
        $this->model = $model;
        $this->headings = $headings;
        $this->querycolumn = $querycolumn;
    }

    /**
     * Get the collection of data to be exported.
     *
     * This method builds a query based on the provided request parameters,
     * filters the data according to the query columns, and retrieves the data.
     *
     * @return \Illuminate\Support\Collection
     */
    public function collection()
    {
        // Create a query builder instance for the model
        $query = $this->model::query();

        // Apply filters based on the request parameters
        foreach ($this->request->all() as $key => $value) {
            if (in_array($key, $this->querycolumn)) {
                $query->where($key, $value);
            }
        }

        // Retrieve and return the filtered data
        return $query->get();
    }

    /**
     * Get the headings for the Excel export.
     *
     * This method returns the headings defined for the export.
     *
     * @return array
     */
    public function headings(): array
    {
        return $this->headings; // Return the defined headings for the export
    }
    public function chunkSize(): int
    {
        // Process data in chunks of 1,000 records
        return 1000;
    }
}
