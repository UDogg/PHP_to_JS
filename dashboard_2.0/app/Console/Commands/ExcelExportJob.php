<?php

namespace App\Console\Commands;

use Illuminate\Console\Command;

class ExcelExportJob extends Command
{
    /**
     * The name and signature of the console command.
     *
     * @var string
     */
    protected $signature = 'excel-export-job';

    /**
     * The console command description.
     *
     * @var string
     */
    protected $description = 'excel export job run jobs stored in queue for larger data excel export ';

    /**
     * Execute the console command.
     */
    public function handle()
    {
        //
        $this->info('Starting to process queued jobs...');
        $this->call('queue:work', [
            '--queue' => 'LargeExcelExports',
            '--stop-when-empty' => true,
        ]);

    }
}
