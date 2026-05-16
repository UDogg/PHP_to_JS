<?php

namespace App\Jobs;

use App\Models\lobMaster;
use App\Models\MongoModel;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Foundation\Bus\Dispatchable;
use Illuminate\Foundation\Queue\Queueable;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Queue\SerializesModels;

class sampleData implements ShouldQueue
{
    use Queueable;

    /**
     * Create a new job instance.
     */
    public function __construct()
    {
        //
    }

    /**
     * Execute the job.
     */
    public function handle(): void
    {
        $lobs=lobMaster::get();
        foreach($lobs as $lob){
            $lob_id = $lob ->id;
            $section = $lob->lob;
            $data = MongoModel::where('section', 'like', $section)->first();
           if(!empty($data)){
            $result = $data->getattributes();
            $res = (!empty($result) ? $result : '');
            if (is_array($res)) {
                $res = json_encode($res); // Convert array to JSON string
            }
            if(!empty($res)){
                $insertSampleData = \App\Models\SampleData::create([
                    'lob_id' => $lob_id,
                    'lob' => $section, 
                    'value' => $res
                ]);
            }
           }
        }
    }
}
