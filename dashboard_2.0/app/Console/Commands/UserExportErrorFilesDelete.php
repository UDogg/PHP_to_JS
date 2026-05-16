<?php

namespace App\Console\Commands;

use App\Models\DataExportLog;
use Illuminate\Console\Command;

class UserExportErrorFilesDelete extends Command
{
    /**
     * The name and signature of the console command.
     *
     * @var string
     */
    protected $signature = 'user-export-error-files-delete';

    /**
     * The console command description.
     *
     * @var string
     */
    protected $description = 'delete daily all the excel error files of user export';

    /**
     * Execute the console command.
     */
    public function handle()
    {
        //
        $files = DataExportLog::select('file','id')->where('file_expiry','<', now())->get();

    }
}
