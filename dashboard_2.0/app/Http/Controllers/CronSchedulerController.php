<?php

namespace App\Http\Controllers;

use App\Models\MasterSchedulerConfig;
use Illuminate\Support\Str;
use Carbon\Carbon;

use Illuminate\Http\Request;

class CronSchedulerController extends Controller
{
    public function index()
    {

        $currentDate = Carbon::now()->toDateString();

        $records = MasterSchedulerConfig::whereDate('starts_on', '<=', $currentDate)
            ->whereDate('ends_on', '>=', $currentDate)
            ->get();

        if ($records->isNotEmpty()) {
            foreach ($records as $record) {
                if ($record->send_at == null) {
                    sendCron();
                    $getid = $record->id;
                    MasterSchedulerConfig::where('id', $getid)->update([
                        'status' => 1,
                    ]);
                } else {
                    $sendAtValue = $record->send_at;
                    $frequencyValue = $record->frequency;
                    $currdate = strtotime($currentDate);  //converting currentDate into seconds
                    $sendAt = strtotime($sendAtValue);
                    $outputDate = $currdate - $sendAt;

                    if ($frequencyValue == 'day') {
                        if ($outputDate > 86400) {        // day in seconds
                            sendCron();
                        }
                    }
                    if ($frequencyValue == 'week') {
                        if ($outputDate > 604800) {       // week in seconds
                            sendCron();
                        }
                    }
                    if ($frequencyValue == 'month') {
                        if ($outputDate > 2628000) {      // month in seconds
                            sendCron();
                        }
                    }
                }
            }
        }
    }
}
