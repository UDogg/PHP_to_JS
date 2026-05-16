<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\Artisan;

class RunMigration extends Controller
{
    public function index(Request $request)
    {
        $path = $request->path;
        if(!empty($path))
        {
            Artisan::call('migrate --path='.$path);
        }
        else
        {
            try {
            Artisan::call('migrate');
            return 'true';
            }
            catch (\Exception $e) {
                return 'false' . $e->getMessage();
            }
        }


    }
    public function dbseed(Request $request)
    {
        $name = $request->name;
        if(!empty($name))
        {
            Artisan::call('db:seed --class='.$name);
            return 'true';
        }
        else
        {
            Artisan::call('db:seed');
            return 'true';

        }


    }
 public function optimizeclear()
    {

        Artisan::call('optimize:clear');
        return 'true';
    }

    public function runJobs(Request $request)
    {
        Artisan::call('queue:work --queue='.$request->name.' --once');
    }

}
