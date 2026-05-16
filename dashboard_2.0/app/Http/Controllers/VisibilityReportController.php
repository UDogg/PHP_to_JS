<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\Http;
use App\helpers;
use Maatwebsite\Excel\Facades\Excel;
use App\Exports\VisibilityReportExport;
use App\webServiceHelper;

class VisibilityReportController extends Controller
{
    public function index()
    {
        return view('visibility_report');
    }
    public function getData(Request $request)
    {
        $data = [];
        $start_date = "";
        $end_date = "";
        if ($request->section == "motor2") {
            $motorData = self::motordata($request);
            if ($motorData['status'] == true) {
                $data = json_decode($motorData['data'])->data;
                $start_date = $motorData['start_date'];
                $end_date = $motorData['end_date'];
            }
        } elseif ($request->section == "health2") {
            $healthData = self::healthData($request);
            if ($healthData['status'] == true) {
                $data = $healthData['data']['data'];
                $start_date = $healthData['start_date'];
                $end_date = $healthData['end_date'];
            }
        } elseif ($request->section == "term") {
            # code...
        } else {
        }

        if ($request->section == "motor2") {
            $section = "motor";
        } elseif ($request->section == "health2") {
            $section = "health";
        } else {
            $section = $request->section;
        }
        return view('visibility_report', compact('data', 'section', 'start_date', 'end_date'));
    }

    public function motordata($request)
    {
  
            // URL to send the request to
            $url = 'https://uatdashboard.rbstaging.in/admin/visibility_report/get_visibility_report';
        
            // Initialize cURL session
        
            // Set the headers
            $headers = [
                'Accept: application/json, text/javascript, */*; q=0.01',
                'Accept-Language: en-US,en;q=0.9',
                'Connection: keep-alive',
                'Content-Type: application/x-www-form-urlencoded; charset=UTF-8',
                'Cookie: enc_sess=0ufv15ufqd0n376tvhsja4vfbju8qf9v',
                'Origin: https://uatdashboard.rbstaging.in',
                'Referer: https://uatdashboard.rbstaging.in/admin/visibility_report',
                'Sec-Fetch-Dest: empty',
                'Sec-Fetch-Mode: cors',
                'Sec-Fetch-Site: same-origin',
                'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36',
                'X-Csrf-Token: null',
                'X-Requested-With: XMLHttpRequest',
                'sec-ch-ua: "Not)A;Brand";v="99", "Google Chrome";v="127", "Chromium";v="127"',
                'sec-ch-ua-mobile: ?0',
                'sec-ch-ua-platform: "Windows"',
            ];
        
            // Set the POST fields
            $postFields = [
                'section' => $request->section,
                'from_date' => $request->from_date,
                'end_date' => $request->end_date,
                'method_new' => $request->method_type,
                'quote_method' => 'revisedquote',
            ];
        
            $data = getWsData($url, $postFields, $headers);

        $start_date = $request['from_date'];
        $end_date = $request['end_date'];

        if (!empty($data)) {
            return [
                'status' => true,
                'data' => $data,
                'start_date' => $start_date,
                'end_date' => $end_date
            ];
        } else {
            return false;
        }
}

    public function motordataview(request $request)
    {

        $section = ($request['data']['section'] ?? $request['section']) == "motor" ? "motor2" : ($request['data']['section'] ?? $request['section']);
        $start_date = ($request['data']['start_date'] ?? $request['start_date']);
        $end_date = ($request['data']['end_date'] ?? $request['end_date']);
        $error_type = ($request['data']['type'] ?? $request['type']);
        $ic = ($request['data']['ic'] ?? $request['ic']);
        $quote_method = "revisedquote";
        $total_record = ($request['data']['record'] ?? $request['record']);

        $url = 'https://uatdashboard.rbstaging.in/admin/visibility_report/download_ic_excel';

        $headers = [
            'Accept: */*',
            'Accept-Language: en-US,en;q=0.9',
            'Connection: keep-alive',
            'Content-Type: application/x-www-form-urlencoded; charset=UTF-8',
            'Cookie: enc_sess=11li5uud6r8mv7sp0t20u21gcd5n9ch7',
            'Origin: https://uatdashboard.rbstaging.in',
            'Referer: https://uatdashboard.rbstaging.in/admin/visibility_report',
            'Sec-Fetch-Dest: empty',
            'Sec-Fetch-Mode: cors',
            'Sec-Fetch-Site: same-origin',
            'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36',
            'X-Csrf-Token: null',
            'X-Requested-With: XMLHttpRequest',
            'sec-ch-ua: "Not)A;Brand";v="99", "Google Chrome";v="127", "Chromium";v="127"',
            'sec-ch-ua-mobile: ?0',
            'sec-ch-ua-platform: "Windows"',
        ];

        $postFields = [
            'section' => $section,
            'from_date' => $start_date,
            'end_date' => $end_date,
            'error_type' => $error_type,
            'ic_name' => $ic,
            'total_record' => $total_record,
            'quote_method' => $quote_method,
            'error_type_api' => 'quote_failed',

           
        ];

        $response = getWsData($url, $postFields, $headers);


        $data = json_encode($response);
        if ($data['status'] == false) {
            return ([
                'status' => 400,
                'data' =>  $data["message"] ?? "No Data Found"
            ]);
        } else {
            return ([
                'status' => 200,
                'data' => $data['data']['list']
            ]);
        }
    }

    public function healthData($request)
    {
        // URL to send the request to
        $url = 'https://uatdashboard.rbstaging.in/admin/visibility_report/get_visibility_report';

        // Set the headers
        $headers = [
            'Accept: application/json, text/javascript, */*; q=0.01',
            'Accept-Language: en-US,en;q=0.9',
            'Connection: keep-alive',
            'Content-Type: application/x-www-form-urlencoded; charset=UTF-8',
            'Cookie: enc_sess=0ufv15ufqd0n376tvhsja4vfbju8qf9v',
            'Origin: https://uatdashboard.rbstaging.in',
            'Referer: https://uatdashboard.rbstaging.in/admin/visibility_report',
            'Sec-Fetch-Dest: empty',
            'Sec-Fetch-Mode: cors',
            'Sec-Fetch-Site: same-origin',
            'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36',
            'X-Csrf-Token: null',
            'X-Requested-With: XMLHttpRequest',
            'sec-ch-ua: "Not)A;Brand";v="99", "Google Chrome";v="127", "Chromium";v="127"',
            'sec-ch-ua-mobile: ?0',
            'sec-ch-ua-platform: "Windows"',
        ];

        // Set the POST fields
        $postFields = [
            'section' => 'health2',
            'from_date' => '2024-06-01',
            'end_date' => '2024-07-01',
            'method_new' => 'proposal',
            'quote_method' => 'revisedquote',
        ];
        $data = getWsData($url, $postFields, $headers);
        return $data;
    }


    public function download(Request $request)
    {
        if (!empty($request->all())) {
            $data = self::motordataview($request);

            if (empty($data['data'])) {
                // Return a JSON response indicating no data was found
                return response()->json(['status' => 'error', 'message' => 'Data not found'], 404);
            }

            $data = $data['data'];
            return Excel::download(new VisibilityReportExport($data), 'motor_data.xlsx');
        } else {
            return response()->json(['status' => 'error', 'message' => 'No data provided'], 400);
        }
    }
}
