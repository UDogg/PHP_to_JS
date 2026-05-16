<?php
namespace App\Console;
use Illuminate\Console\Scheduling\Schedule;
use Illuminate\Foundation\Console\Kernel as ConsoleKernel;
use App\Console\PolicyStatusExportZipClear;
class Kernel extends ConsoleKernel
{
    /**
     * The Artisan commands provided by your application.
     *
     * @var array
     */


    /**
     * Define the application's command schedule.
     *
     * @param  \Illuminate\Console\Scheduling\Schedule  $schedule
     * @return void
     */
    protected function schedule(Schedule $schedule)
    {

        ##clear zip files from storage
        $schedule->command('PolicyStatusExportZipClear')->daily();
        $schedule->command('excel-export-job')->daily();
        $schedule->command('user-export-error-files-delete')->daily();
    }

    /**
     * Register the commands for the application.
     *
     * @return void
     */





}
