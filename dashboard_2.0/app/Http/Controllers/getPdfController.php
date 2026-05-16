<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\helpers;
class getPdfController extends Controller
{

    public function getPdf(Request $request)
    {



    //for motor data
    // {
    //     "company": "iffco tokio general insurance co. ltd.",
    //     "section": "bike",
    //     "policy": "",
    //     "trace_id": "2024081700035515"
    //   } 

    // for health
    // {
    //     "trace_id":"1226162807912836 - P:244",
    //     "proposal_id":"244"
    // }



       $url = "https://api-uat.nammacover.com/api/v1/dashboard/pdf_details";
       $requestData = $request->all();
       $data = getWsData($url, $requestData);

       if (!empty($data)) {
        $data = json_decode($data);
        if (($data->status) ?? '' == 200) {

            return ([
                'status' => $data->status,
                'message' => $data->message,
                'data' => $data->data
            ]);

        } else {
            return ([
                'status' => $data->status ?? 500,
                'message' => $data->message ?? 'api error',
            ]);
        }
       }

    }
}
