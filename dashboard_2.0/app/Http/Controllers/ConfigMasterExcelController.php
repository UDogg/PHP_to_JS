<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use PhpOffice\PhpSpreadsheet\Spreadsheet;
use PhpOffice\PhpSpreadsheet\Writer\Xlsx;
use Illuminate\Support\Facades\DB;
use Symfony\Component\HttpFoundation\StreamedResponse;
use PhpOffice\PhpSpreadsheet\IOFactory;
use Carbon\Carbon;

class ConfigMasterExcelController extends Controller
{
    public function downloadConfigSettingsExcel()
    {
        return response()->streamDownload(function () {

        $spreadsheet = new \PhpOffice\PhpSpreadsheet\Spreadsheet();
        $sheet = $spreadsheet->getActiveSheet();
    
        $sheet->fromArray([
            'Credential ID',
            'Credential Label',
            'Credential Key',
            'Credential Value',
            'Configuration',
            'Environment',
            'Created At',
            'Updated At'
        ], null, 'A1');
    
        $rowIndex = 2;
    
        DB::table('config_settings')
            ->whereNull('deleted_at')
            ->orderBy('credential_id')
            ->chunk(1000, function ($rows) use (&$sheet, &$rowIndex) {
                foreach ($rows as $row) {
                    $sheet->fromArray([
                        $row->credential_id,
                        credential_decrypt($row->credential_label),
                        credential_decrypt($row->credential_key),
                        credential_decrypt($row->credential_value),
                        $row->configuration,
                        $row->enviroment,
                        $row->created_at,
                        $row->updated_at,
                    ], null, 'A' . $rowIndex++);
                }
            });
    
        $writer = new \PhpOffice\PhpSpreadsheet\Writer\Xlsx($spreadsheet);
        $writer->save('php://output');

    }, 'Config_Settings_' . now()->format('Ymd_His') . '.xlsx');

    }

        
    public function uploadConfigSettingsCsv(Request $request)
    {
        // $request->validate([
        //     'file' => 'required|mimes:csv,txt'
        // ]);
    
        DB::beginTransaction();
    
        try {
    
            $file = $request->file('file');
            $handle = fopen($file->getRealPath(), 'r');
    
            if ($handle === false) {
                throw new \Exception('Unable to read CSV file');
            }
    
            // Skip header row
            fgetcsv($handle);
    
            while (($row = fgetcsv($handle)) !== false) {
    
            
                $credentialId    = $row[0] ?? null;
                $credentialLabel = $row[1] ?? null;
                $credentialKey   = $row[2] ?? null;
                $credentialValue = $row[3] ?? null;
                $configuration   = $row[4] ?? null;
                $environment     = $row[5] ?? null;
                $createdAt = $this->normalizeDate($row[6] ?? null);
    
                // Skip empty rows
                if (empty($credentialKey)) {
                    continue;
                }
    
                $payload = [
                    'credential_label' => $credentialLabel,
                    'credential_key'   => $credentialKey,
                    'credential_value' => credential_encrypt($credentialValue),
                    'configuration'    => $configuration,
                    'enviroment'       => $environment,
                    'updated_at'       => now(),
                ];
                
    
                if (!empty($credentialId) &&
                    DB::table('config_settings')->where('credential_id', $credentialId)->exists()
                ) {
                    // UPDATE
                    DB::table('config_settings')
                        ->where('credential_id', $credentialId)
                        ->update($payload);
                } else {
                    // INSERT
                    $payload['created_at'] = $createdAt;
    
                    DB::table('config_settings')->insert($payload);
                }
            }
    
            fclose($handle);
            DB::commit();
    
            return response()->json([
                'status' => true,
                'message' => 'CSV imported successfully'
            ]);
    
        } catch (\Exception $e) {
    
            DB::rollBack();
    
            return response()->json([
                'status' => false,
                'message' => 'CSV import failed',
                'error' => $e->getMessage()
            ], 500);
        }
    }

     function normalizeDate($value)
    {
        if (empty($value)) {
            return now();
        }
    
        try {
            return Carbon::createFromFormat('d-m-Y H:i', trim($value))
                ->format('Y-m-d H:i:s');
        } catch (\Exception $e) {
            return now();
        }
    }
}
