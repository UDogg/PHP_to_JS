<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;

class SqlRunnnerController extends Controller
{
    //
    public static function index()
    {
        return view('sql_runner');
    }
    public static function ExecuteSql(Request $req)
    {
        $hostname = env('DB_HOST');
        $username  = env('DB_USERNAME');
        $password = env('DB_PASSWORD');
        $db = env('DB_DATABASE');
        $connection = mysqli_connect($hostname,$username,$password,$db);
        if(!$connection) {
           return  response()->json()->json(['status' => 500, 'message' => 'Connection Failed To Database']);
        }
        $res = $req->all();
        $res = $res['query'];
        $invalid_keys_arr = ['drop','alter','update','create','insert','delete'];
        foreach ($invalid_keys_arr as $key)
        {
            $invalid_keys = strpos($res,$key);
            if($invalid_keys)
            {
               return  response()->json()->json(['status' => 500, 'message' => 'Invalid Sql Query']);
            }
        }
        $result = mysqli_query($connection, $res);
        $number_of_rows = mysqli_num_rows($result);
        if($number_of_rows > 0)
        {
            $result = mysqli_fetch_all($result, MYSQLI_ASSOC);
        }
        $columns = array_keys($result[0]);
        mysqli_close($connection);
        $connection = $res = $invalid_keys = $invalid_keys_arr = '';
        return view('sql_runner',compact('columns','result'));

    }
}
