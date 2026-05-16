<?php

namespace App\Http\Controllers\MasterPolicy;

use App\Http\Controllers\Controller;
use App\Mail\RaiseQueryMail;
use App\Models\EmailTemplate;
use App\Models\MongoModel;
use App\Models\StagemasterModel;
use App\Models\substagemaster;
use Illuminate\Http\Request;
use GuzzleHttp\Client;
use GuzzleHttp\Psr7\Request as Ghttp;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Facades\Mail;
use MongoDB\BSON\Regex;
use Illuminate\Support\Facades\Log;
use Exception;
use Illuminate\Support\Facades\Http;


class PolicyUploadController extends Controller
{
    public function uploadPolicyData(Request $request)
    {

        $validator = Validator::make($request->all(), [
            'trace_id' => 'required',
            'policy_no' => 'required',
            'file' => 'required|file|mimes:pdf,jpg,jpeg,png',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'errors' => $validator->errors(),
            ], 422);
        }

        $auth = Auth::id();

        $stageNumber = StagemasterModel::Where('stage_name', 'Booking Pending')->pluck('sub_stage_name')->first();

        $stageArray =  array_filter(explode(',', $stageNumber));

        $subStages = substagemaster::whereIn('id', $stageArray)->pluck('sub_stage_name');

        $data = MongoModel::where('trace_id', $request->trace_id)->whereIn('transaction_stage', $subStages)->first();  

        if (empty($data)) {
            return response()->json([
                "status" => false,
                "message" => "No Data Found"
            ], 404);
        }

        if (empty(trim($data->section))) {
            return response()->json([
                "status" => false,
                "message" => "No section Found for this Trace ID"
            ], 404);
        }

        $requestedSection = strtoupper($data->section);

        $motorLob = ['CAR', 'BIKE', 'MISC', 'GCV', 'PCV', 'MOTOR'];
        $healthLob = ['HEALTH', 'TOP_UP'];

        if (in_array($requestedSection, $motorLob)) {
            $requestedSection = 'MOTOR';
        }
        if (in_array($requestedSection, $healthLob)) {
            $requestedSection = 'HEALTH';
        }

        if (trim($requestedSection) == 'HEALTH') {
            $apiUrl = config('Policy.Upload.Pdf.Health');
        } else if (trim($requestedSection) == 'MOTOR') {
            $apiUrl = config('Policy.Upload.Pdf.Motor');
        }

        $content = base64_encode(file_get_contents($request->file)); // Base64 content

        $headers = [
            'accept' => 'application/json',
            'Content-Type' => 'application/json'
        ];

        $methodType = 'POST';
        $body = [
            "section" => strtolower($requestedSection),
            "policy_number" => $request->policy_number ?? null,
            "trace_id" => $request->trace_id,
            "screenshotFile" => $request->file->getClientOriginalName(),
            "screenshot_content" => $content,
            "ss_type" => $request->file->getClientOriginalExtension(),
            "user_id" => $auth,

        ];

        try {

            $client = new Client();
            $jsonBody = json_encode($body);
            $newRequest = new Ghttp($methodType, $apiUrl, $headers, $jsonBody);
            $response = $client->sendAsync($newRequest)->wait();
            $result = $response->getBody($apiUrl);
            $data = json_decode($result, true);

            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $data,
                    $response->getStatusCode(),
                    $headers,
                    $apiType = 'PDF-UPLOAD-MOTOR'
                );
            }

            return $data;
        } catch (\Exception $e) {
            if (config('store_api_logs') == true) {
                logApiRequestResponse(
                    $apiUrl,
                    $methodType,
                    $body,
                    $e->getMessage(),
                    $e->getCode() ?? 500,
                    $headers,
                    $apiType = 'PDF-UPLOAD-MOTOR'

                );
            }
            return response()->json([
                'status' => 500,
                'message' => "Something went wrong",
                'error' => $e->getMessage()
            ]);
        }
    }

    public function raiseQuery(Request $request)
    {

        if (!$request->has('trace_id') ) {
            return response()->json([
                "status" => false,
                "message" => "Trace ID Not Provided"
            ], 404);
        }

        $mongoData = MongoModel::where('trace_id', $request->trace_id)->first();

        if (empty($mongoData)) {
            return response()->json([
                'status' => 500,    
                'message' => "Data related to this Trace Id do not Exist",
            ]);
        }

        $seller_Id = $mongoData->seller_id;
        $seller_type = $mongoData->seller_type;

        $auth_user = Auth::user();
        $auth_user->id = 18;

        if (!($auth_user->is_admin == 'Y' && $auth_user->usertype == '1')) {
            $lowerHierarcyofLoggedInUser = getUserLowerHierarchyWithMapping($auth_user->id);

            $check = in_array($seller_Id, $lowerHierarcyofLoggedInUser);
            if (!$check) {
                return response()->json([
                    'status' => 500,
                    'message' => "Not Authorized to Access this Resource",
                ]);
            }
        }

        $stageName = subStageTostage($mongoData->transaction_stage);

        $template = EmailTemplate::where('stage', $stageName)->first();
        $topic = explode(':', $template->subject)[0];
    
        $data = [
            'topic' => $topic,
            'customer_name' => $mongoData->proposer_name,
            'proposal_number' => $mongoData->proposal_no,
            'trace_id' => $mongoData->trace_id,
            'insurance_company' => $mongoData->company_name,
            'inspection_number' => $mongoData->breakin_number, 
            'registration_number' => $mongoData->vehicle_registration_number,
            'related_to' => $mongoData->transaction_stage, //'Policy PDF Download', // list of common issues daal na hay but ye apan shatad nahi denge
            // 'transaction_number' => 'TXN7890', // //transaction_date
            'policy_number' => $mongoData->policy_no,
            'user_id' => $mongoData->seller_mobile, 
            'name' => $mongoData->seller_name, 
            'email' => $mongoData->seller_email,
            'remark' => $request->input('remark', ''),
        ];

        $body = $template->body;
        $sendTo = config('RaiseQuerySendMailTo');

        foreach ($data as $key => $value) {
            $body = str_replace("{" . $key . "}", $value, $body);
        }

        $htmlBody = nl2br(strip_tags($body, '<b><br><p><strong><ul><li>'));
        $subject = ($template->subject ?? 'Raise Query - ' . $data['topic']) . ' | Trace ID: ' . $mongoData->trace_id;

        Mail::to($sendTo)->send(new RaiseQueryMail($subject, $htmlBody)); // Mailing to karo 
        EmailActivityLog($auth_user,null,null,$subject,$body,$data['email']);
        //Mailing to user
        // $userData = [
        //     'trace_id' => $mongoData->trace_id,
        //     // 'issue_title' => 'Policy Document Not Received',
        //     'customer_name' => $mongoData->proposer_name,
        //     'logo_url' => asset('images/karoinsure-logo.png'),
        // ];

        // $userTemplate = EmailTemplate::where('stage', 'Customer')->first();
        // $userSubject = $userTemplate->subject ?? 'User Policy Status' ;
        // $userBody = $userTemplate->body;

        //  foreach ($userData  as $key => $value) {
        //     $userBody = str_replace("{" . $key . "}", $value, $userBody);
        //     $userSubject = str_replace("{" . $key . "}", $value, $userSubject);
        // }

        // $userHtmlBody = nl2br(strip_tags($userBody, '<b><br><p><strong><ul><li>'));
        // Mail::to($mongoData->proposer_emailid)->send(new RaiseQueryMail($userSubject, $userHtmlBody)); 

        return response()->json([
            'status' => 200,
            'message' => "Email Sent Successfully",
        ], 200);
    }
    public function sharePdf(Request $request){
        try {
        $api = config("shared_pdf_api");
        if (empty($api)) {
            return response()->json([
                'status' => false,
                'message' => 'API URL not configured.'
            ], 500);
        }
        $rules =[
            'enquiryId' =>'required',
        ];
        $validator = Validator::make(request()->all(),$rules);
        if ($validator->fails()) {
            return response()->json([
                'status' => false,
                'message' => 'Validation failed.',
                'errors' => $validator->errors(),
            ], 422);
        }
        $payload = [
            'enquiryId'  => $request->enquiryId,
            'email'      => $request->email,
            'sms'        => $request->sms,
            'whatsapp'   => $request->whatsapp
        ];
        $response = Http::timeout(60)->post($api,$payload);
        if ($response->successful()) {

            return response()->json([
                'status' => true,
                'data' => $response->json(),
            ]);

        }

        return response()->json([
            'status' => false,
            'message' => 'API request failed',
        ], $response->status());

    } catch (Exception $e) {
        Log::error('API error in updateDocuments: ' . $e->getMessage());

        return response()->json([
            'status' => false,
            'message' => 'Error connecting to API',
            'error' => $e->getMessage(),
        ], 500);
    }
    }
}


