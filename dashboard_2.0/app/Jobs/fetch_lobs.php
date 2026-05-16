<?php

namespace App\Jobs;

use App\Models\MongoModel;
use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Foundation\Bus\Dispatchable;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Queue\SerializesModels;
Use App\Models\substagemaster;

class fetch_lobs implements ShouldQueue
{
    use Dispatchable, InteractsWithQueue, Queueable, SerializesModels;

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
        //
        $get_all_sub_Stage = array_column(\App\Models\substagemaster::select('sub_stage_name')->get()->toArray(),'sub_stage_name');
        $data = \App\Models\MongoModel::distinct('transaction_stage')->get()->all() ;
        foreach ($data as $key => $value)
        {
            $result = $value->getattributes();
            $res = (!empty($result) ? $result[0] : '');
            if(!in_array($res, $get_all_sub_Stage) && !empty($res))
            {
                $init_sub_stage = \App\Models\substagemaster::create([
                    'sub_stage_name' => $res
                ]);
            }
        }


    }
}
