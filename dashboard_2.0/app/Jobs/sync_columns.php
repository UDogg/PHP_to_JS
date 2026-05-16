<?php

namespace App\Jobs;

use App\Models\lobMaster;
use App\Models\MongoModel;
use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Foundation\Bus\Dispatchable;
use Illuminate\Queue\InteractsWithQueue;
use Illuminate\Queue\SerializesModels;

class sync_columns implements ShouldQueue
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
        $lobs = array_column(lobMaster::select('lob','is_enabled','id')->where('is_enabled','Y')->get()->toArray(),'lob','id');
        foreach($lobs as $k => $l)
        {
            $mongodata = MongoModel::where('section',$l)->first();
            $mongodata = !empty($mongodata) ? $mongodata->toArray() : [];
            if(!empty($mongodata))
            {
                $policy_status_column_config = \Illuminate\Support\Facades\DB::table('policystatus_column_master')->select('column_name','lob')->where('lob',$k)->get()->toArray();
                $policy_columns_Arr =  [];
                if(!empty($policy_status_column_config))
                {
                    foreach ($policy_status_column_config as $pol_key => $pol_value) {
                        array_push($policy_columns_Arr, $pol_value->column_name);
                    }
                    foreach ($mongodata as $key => $value)
                    {
                        if(!in_array($key, $policy_columns_Arr))
                        {
                            $ins = \Illuminate\Support\Facades\DB::table('policystatus_column_master')->insert([
                                'column_name' => $key,
                                'lob' => $k,
                            ]);
                        }
                    }
                }
                else
                {
                    foreach ($mongodata as $key => $value)
                    {
                        $ins = \Illuminate\Support\Facades\DB::table('policystatus_column_master')->insert([
                            'column_name' => $key,
                            'lob' => $k,
                        ]);
                    }

                }
            }
//                for memory management
            $mongodata = $policy_status_column_config = $key = $value = $ins = $policy_columns_Arr = null;

        }


    }
}
