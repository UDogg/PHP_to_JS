<?php

namespace App\Http\Controllers;

use App\Models\ExcelDownloadLog;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Storage;

class mispReportDownloadController extends Controller
{
    //
    private $Auth;
    public function __construct()
    {
        $this->Auth = Auth::user();
    }
    public function  index()
    {
        $arrayStatus = [
            '0' => 'Pending',
            '1' => 'Progress',
            '2' => 'Success',
            '3' => 'Failed',

        ];
        $allData = ExcelDownloadLog::where('user_id', $this->Auth->id)->select('file_name','source','status','created_at')->get();
        $allData = $allData->map(function ($item) use($arrayStatus) {
            $item->file_name = !empty($item->file_name) ? Storage::disk('public')->url($item->file_name) : '';
            $item->status = array_key_exists($item->status,$arrayStatus) ? $arrayStatus[$item->status] : $item->status ;
            return $item;
        });
        return response()->json($allData);
    }
}
