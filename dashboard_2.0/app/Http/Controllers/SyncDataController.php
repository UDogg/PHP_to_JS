<?php

namespace App\Http\Controllers;

use App\Jobs\sync_columns;
use Illuminate\Http\Request;
use App\Jobs\fetch_lobs;
use App\Jobs\sampleData;
use \Illuminate\Support\Facades\Artisan;

class SyncDataController extends Controller
{
    /**
     * Handle the incoming request.
     */
    public function __invoke(Request $request)
    {
        sync_columns::dispatchSync();
        fetch_lobs::dispatchSync();
        sampleData::dispatchSync();
//       Artisan::call(' queue:work ');
        return response()->json([
            'message' => 'sub stage sync done from mongo',
            'status' => 200
        ]);
    }
}
