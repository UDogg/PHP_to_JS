<?php

namespace App\Exports;

use App\Models\SmsActivityLog;
use Maatwebsite\Excel\Concerns\FromCollection;
use Maatwebsite\Excel\Concerns\WithHeadings;

class SmsActivityLogsExport implements FromCollection, WithHeadings
{
    public function collection()
    {
        return SmsActivityLog::select('id', 'mobile', 'message', 'type', 'status', 'sent_at', 'user_id')->get();
    }

    public function headings(): array
    {
        return ['ID', 'Mobile', 'Message', 'Type', 'Status', 'Sent At', 'User ID'];
    }
}
