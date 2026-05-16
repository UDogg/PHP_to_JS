<?php

namespace App\Exports;

use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithMapping;
use Maatwebsite\Excel\Concerns\WithHeadings;

class VisibilityReportExportData implements FromCollection, WithMapping, WithHeadings
{
    protected $data;

    public function __construct($data)
    {
        $this->data = $data;
    }

    /**
     * Convert the provided data into a collection.
     */
    public function collection()
    {
        return collect($this->data);
    }

    /**
     * Map the data rows for export.
     */
    public function map($row): array
    {
        return [
            $row['Logs link'] ?? '',
            $row['enquiry_id'] ?? '',
            $row['ic_name'] ?? '',
            $row['vehicle_type'] ?? '',
            $row['make'] ?? '',
            $row['model'] ?? '',
            $row['variant'] ?? '',
            $row['version_id'] ?? '',
            $row['fuel_type'] ?? '',
            $row['vehicle_register_date'] ?? '',
            $row['manufacture_year'] ?? '',
            $row['insurer_modelid'] ?? '',
            $row['lead_id'] ?? '',
            $row['quote_reference_no'] ?? '',
            $row['insurer_quote_id'] ?? '',
            $row['response_time'] ?? '',
            $row['previous_policy_type'] ?? '',
            $row['previous_policy_expiry_date'] ?? '',
            $row['case_type'] ?? '',
            $row['plan_name'] ?? '',
            $row['policy_type'] ?? '',
            $row['rto'] ?? '',
            $row['idv'] ?? '',
            $row['quote_response'] ?? '',
            $row['actionable_at'] ?? '',
            $row['error_type'] ?? '',
            $row['error_category'] ?? '',
            $row['premium'] ?? '',
            $row['Date'] ?? '',
            $row['Time'] ?? '',
            $row['registration_number'] ?? '',
        ];
    }

    /**
     * Define the headings for the Excel sheet.
     */
    public function headings(): array
    {
        return [
            'Logs Link',
            'Enquiry ID',
            'IC Name',
            'Vehicle Type',
            'Make',
            'Model',
            'Variant',
            'Version ID',
            'Fuel Type',
            'Vehicle Register Date',
            'Manufacture Year',
            'Insurer Model ID',
            'Lead ID',
            'Quote Reference No',
            'Insurer Quote ID',
            'Response Time',
            'Previous Policy Type',
            'Previous Policy Expiry Date',
            'Case Type',
            'Plan Name',
            'Policy Type',
            'RTO',
            'IDV',
            'Quote Response',
            'Actionable At',
            'Error Type',
            'Error Category',
            'Premium',
            'Date',
            'Time',
            'Registration Number',
        ];
    }
}
