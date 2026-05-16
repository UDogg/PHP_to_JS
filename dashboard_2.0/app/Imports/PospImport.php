<?php

namespace App\Imports;

use App\Models\Broker;
use App\Models\User;
use Maatwebsite\Excel\Concerns\ToCollection;
use Maatwebsite\Excel\Concerns\WithHeadingRow;
use Illuminate\Support\Collection;

class PospImport implements ToCollection, WithHeadingRow
{
    public $validRecords = [];
    public $failedRecords = [];
    public $successCount = 0;
    public $failedCount = 0;

    public function collection(Collection $rows)
    {
        $users = User::select('id', 'mobile', 'name')->get();

        // Decrypt and create a mapping for faster lookup
        $userMap = [];
        foreach ($users as $user) {
            $decryptedMobile = credential_decrypt($user->mobile);
            $decryptedName = credential_decrypt($user->name);

            // Store users in an array indexed by mobile & name
            $userMap[$decryptedMobile][$decryptedName] = $user->id;
        }

        foreach ($rows as $row) {
            // Ensure required fields exist
            if (!isset($row['user_code'], $row['user_name'])) {
                continue; // Skip invalid rows
            }

            $importedMobile = $row['user_code'];
            $importedName = $row['user_name'];

            $errorReason = [];

            if (!isset($userMap[$importedMobile])) {
                $errorReason[] = "Mobile number not found";
            }

            if (!isset($userMap[$importedMobile][$importedName])) {
                $errorReason[] = "Username not found";
            }

            // Check if both mobile & name exist in our decrypted user map
            if (empty($errorReason)) {
                $this->successCount++;
                $this->validRecords[] = [
                    'mobile' => $importedMobile,
                    'label' => $importedName,
                    'value' => $userMap[$importedMobile][$importedName] ?? null
                ];
            } else {
                $this->failedCount++;
                $this->failedRecords[] = [
                    'mobile' => $importedMobile,
                    'label' => $importedName,
                    'value' => $userMap[$importedMobile][$importedName] ?? null,
                    'error_reason' => implode(', ', $errorReason)
                ];
            }
        }
    }
}
