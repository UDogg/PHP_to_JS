<?php

namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;
use App\Models\Broker;
use App\Models\PartnerUserMapping;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use App\Exports\AllDataExport;
use Illuminate\Support\Facades\Auth;
use Maatwebsite\Excel\Facades\Excel;
use Illuminate\Support\Facades\Storage;
use App\Services\FileService;
use Illuminate\Http\Exceptions\HttpResponseException;

class BrokerController extends Controller
{
    /**
     * Display a listing of the resource.
     */
    public function __constructor()
    {
        $this->user = Auth::user();
        if(!$this->user->can('broker.view'))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
    }
    public function index()
    {
        $broker = Broker::select('broker_id','broker_name', 'category','cin_no','address','contact_no','email','irdia_registration_no','favicon_icon','logo','sign_in_option','status','captacha_configure','is_email','is_sms','default_otp','master_otp','front_logo','marquee')->orderBy('broker_id','desc')->latest();
        $columns = $broker;
        $broker_count = $broker->get();
        $columns = $broker;
        $broker = $broker->get();
        if(count($broker_count) != 0) {
            $columns = $broker;
            $columns = array_keys($columns->first()->toArray());

        } else {
            $columns = ['broker_id','broker_name', 'category','cin_no','address','contact_no','email','irdia_registration_no','favicon_icon','logo','sign_in_option','status','captacha_configure','is_email','is_sms','default_otp','master_otp','front_logo','marquee'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'broker_id') {
                unset($columns[$key]);
            } elseif ($value === 'broker_name') {
                $columns[$key] = 'Broker Name';
            } elseif ($value === 'cin_no') {
                $columns[$key] = 'Cin No';
            }elseif ($value === 'irdia_registration_no') {
                $columns[$key] = 'Irdia Registration No';
            }elseif ($value === 'favicon_icon') {
                $columns[$key] = 'Favicon Icon';
            }elseif ($value === 'sign_in_option') {
                $columns[$key] = 'Sign In Option';
            }elseif ($value === 'contact_no') {
                $columns[$key] = 'Contact No';
            }elseif ($value === 'category') {
                $columns[$key] = 'Category';
            }elseif ($value === 'address') {
                $columns[$key] = 'Address';
            }elseif ($value === 'email') {
                $columns[$key] = 'Email';
            }elseif ($value === 'logo') {
                $columns[$key] = 'Logo';
            }elseif ($value === 'status') {
                $columns[$key] = 'Status';
            }elseif ($value === 'captacha_configure') {
                $columns[$key] = 'Captcha Configure';
            }elseif ($value === 'is_email') {
                $columns[$key] = 'Is Email';
            }elseif ($value === 'is_sms') {
                $columns[$key] = 'Is Sms';
            }elseif ($value === 'default_otp') {
                $columns[$key] = 'Default Otp';
            }elseif ($value === 'master_otp') {
                $columns[$key] = 'Master Otp';
            }elseif ($value === 'front_logo'){
                $columns[$key] = 'Front logo';
            }elseif($value === 'marquee'){
                $columns[$key] = 'Marquee';
            }else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }
        //$app_key = env('APP_KEY');
        // foreach ($broker as $broker) {
        //     $broker->credential_value = credential_decrypt($broker->credential_value);

        // }

        if ($broker->isEmpty()) {
            return redirect()->route('broker.create');
        }
        return view('broker.index', compact('columns', 'broker'));
    }

    /**
     * Show the form for creating a new resource.
     */
    public function create()
    {
        return view('broker.create');
    }

    /**
     * Store a newly created resource in storage.
     */
    public function store(Request $request)
    {
        // if (!$this->user->can('broker.edit')) {
        //     return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        // }
        $rules = [
            'broker_name' => 'required|string|max:255',
            'category' =>'required',
            'irdia_registration_no' => 'required|string|digits:3|unique:broker,irdia_registration_no',
            'email' => 'required|email',
            'contact_no' => 'required|digits:10',
            'cin_no' => 'required',
            'address' => 'required',
            'logo' => 'required|mimes:jpeg,png,jpg|max:2048',
            'favicon_icon' => 'required|mimes:jpeg,png,jpg|max:2048',
            'sign_in_option' => 'required|array',
            'sign_in_option.*' => 'string',
            'captacha_configure' => 'required|in:On,Off',
            'is_email' => 'required|in:Y,N',
            'is_sms' => 'required|in:Y,N',
            'default_otp' => 'required|in:Y,N',
            'master_otp' => 'required_if:default_otp,Y',
            'front_logo' => 'required|mimes:jpeg,png,jpg,svg|max:2048',
            'marquee' => 'required|in:Y,N',
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{

                if ($request->hasFile('logo')) {
                    $logoFile = $request->file('logo');
                    $logoFileName = 'logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
                    $logoPath = $request->file('logo')->storeAs('broker_logo', $logoFileName, 'public');
                }else{
                    return redirect()->back()->withErrors([
                        'message' => 'Error While Storing the file.',
                    ])->withInput();
                }

                if ($request->hasFile('favicon_icon')) {
                    $favIconFile = $request->file('favicon_icon');
                    $favIconFileName = 'favicon_icon_' . time() . '.' . $favIconFile->getClientOriginalExtension();
                    $favIconPath = $request->file('favicon_icon')->storeAs('broker_favicon', $favIconFileName, 'public');
                }else{
                    return redirect()->back()->withErrors([
                        'message' => 'Error While Storing the file.',
                    ])->withInput();
                }

                if ($request->hasFile('front_logo')) {
                    $frontlogoFile = $request->file('front_logo');
                    $frontlogoFileName = 'front_logo_' . time() . '.' . $frontlogoFile->getClientOriginalExtension();
                    $frontlogoPath = $request->file('front_logo')->storeAs('broker_front_logo', $frontlogoFileName, 'public');
                }else{
                    return redirect()->back()->withErrors([
                        'message' => 'Error While Storing the file.',
                    ])->withInput();
                }
            $sign_in_options = implode(',', $request->input('sign_in_option'));
            $broker = new Broker();
            $broker->broker_name = $request->broker_name;
            $broker->category = $request->category;
            $broker->irdia_registration_no = $request->irdia_registration_no;
            $broker->email = $request->email;
            $broker->contact_no = $request->contact_no;
            $broker->cin_no = $request->cin_no;
            $broker->address = $request->address;
            $broker->logo = $logoPath;
            $broker->favicon_icon = $favIconPath;
            $broker->sign_in_option = $sign_in_options;
            $broker->captacha_configure = $request->input('captacha_configure');
            $broker->is_email = $request->input('is_email');
            $broker->is_sms = $request->input('is_sms');
            $broker->default_otp = $request->input('default_otp');
            $broker->master_otp = $request->input('master_otp');
            $broker->front_logo = $frontlogoPath;
            $broker->marquee = $request->marquee;

            $broker->save();
            if ($broker->save()==true) {
                return redirect()->route('broker.index')->with([
                    'message' => 'Session Created Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating User.',
                ])->withInput();
            }
        }
    }

    /**
     * Display the specified resource.
     */
    public function show($id)
    {
        $broker = Broker::findOrFail($id);
        return view('broker.show', compact('broker'));
    }

    /**
     * Show the form for editing the specified resource.
     */
    public function edit(Broker $broker)
    {
        return view('broker.edit', compact('broker'));
    }

    /**
     * Update the specified resource in storage.
     */
    public function update(Request $request, Broker $broker, FileService $files)
{
    $rules = [
        'broker_name' => 'required|string|max:255',
        'category' =>'required',
        'irdia_registration_no' => 'required|string|digits:3',
        'email' => 'required|email',
        'contact_no' => 'required|digits:10',
        'cin_no' => 'required',
        'address' => 'required',
        'logo' => 'nullable|mimes:jpeg,png,jpg|max:2048',
        'favicon_icon' => 'nullable|mimes:jpeg,png,jpg|max:2048',
        'sign_in_option' => 'required|array',
        'sign_in_option.*' => 'string',
        'captacha_configure' => 'required|in:On,Off',
        'is_email' => 'required|in:Y,N',
        'is_sms' => 'required|in:Y,N',
        'default_otp' => 'required|in:Y,N',
        'master_otp' => 'required_if:default_otp,Y',
        'front_logo' => 'nullable|mimes:jpeg,png,jpg|max:2048',
        'marquee' => 'required|in:Y,N'
    ];

    $validator = Validator::make($request->all(), $rules);

    if ($validator->fails()) {
        return redirect()->back()->withErrors($validator->errors())->withInput();
    }

    if ($request->hasFile('logo')) {
        $logoFile = $request->file('logo');
        // $logoFileName = 'logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
        $logoFileName = 'broker_logo/logo_' . time() . '.' . $logoFile->getClientOriginalExtension();
        // $logoPath = $logoFile->storeAs('broker_logo', $logoFileName, 'public');
        $files->upload($logoFileName, file_get_contents($logoFile));
        $fullUrl = $files->url($logoFileName);
        $broker->logo = parse_url($fullUrl, PHP_URL_PATH);
    }

    if ($request->hasFile('favicon_icon')) {
        $favIconFile = $request->file('favicon_icon');
        $favIconFileName = 'broker_favicon/favicon_icon_' . time() . '.' . $favIconFile->getClientOriginalExtension();
        $files->upload($favIconFileName, file_get_contents($favIconFile));
        $fullUrl = $files->url($favIconFileName);
        $broker->favicon_icon = parse_url($fullUrl, PHP_URL_PATH);
    }
    if ($request->hasFile('front_logo')) {
        $frontlogoFile = $request->file('front_logo');
        $frontlogoFileName = 'broker_front_logo/front_logo_' . time() . '.' . $frontlogoFile->getClientOriginalExtension();
        $files->upload($frontlogoFileName, file_get_contents($frontlogoFile));
        $fullUrl = $files->url($frontlogoFileName);
        $broker->front_logo = parse_url($fullUrl, PHP_URL_PATH);
    }
    
    $sign_in_options = implode(',', $request->input('sign_in_option'));

    $broker->broker_name = $request->broker_name;
    $broker->category = $request->category;
    $broker->irdia_registration_no = $request->irdia_registration_no;
    $broker->email = $request->email;
    $broker->contact_no = $request->contact_no;
    $broker->cin_no = $request->cin_no;
    $broker->address = $request->address;
    $broker->sign_in_option = $sign_in_options;
    $broker->captacha_configure = $request->input('captacha_configure');
    $broker->is_email = $request->input('is_email');
    $broker->is_sms = $request->input('is_sms');
    $broker->default_otp = $request->input('default_otp');
    $broker->master_otp = $request->input('master_otp');
    $broker->marquee = $request->input('marquee');

    if ($broker->save()) {
        return redirect()->route('broker.index')->with([
            'message' => 'Broker updated successfully.',
            'class' => 'success',
        ]);
    } else {
        return redirect()->back()->withErrors([
            'message' => 'Error while updating broker.',
        ])->withInput();
    }
}

    /**
     * Remove the specified resource from storage.
     */
    public function destroy(string $id)
    {
        if (!$this->user->can('broker.edit')) {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $broker = Broker::find($id);
        if ($broker->delete()) {
            return redirect()->route('broker.index')->with([
                'message' => 'broker Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('broker.index')->with([
                'message' => 'Error While Deleting the broker.',
                'class' => 'danger',
            ]);
        }
    }

    /**
     * Broker Details Api
     */

    public function createBroker(Request $request)
    {
        $validated = $request->validate([
            'broker_name' => 'required|string|max:255',
            'category' => 'nullable|string|max:255',
            'cin_no' => 'nullable|string|max:255',
            'address' => 'nullable|string|max:255',
            'contact_no' => 'nullable|string|max:20',
            'email' => 'nullable|email|max:255',
            'irdia_registration_no' => 'nullable|string|max:255',
            'favicon_icon' => 'nullable|string|max:255',
            'logo' => 'nullable|string|max:255',
            'city' => 'nullable|string|max:255',
            'state' => 'nullable|string|max:255',
            'meta_title' => 'nullable|string',
            'meta_description' => 'nullable|string'
        ]);
        $broker = new Broker();
        $broker->broker_name = $request->broker_name;
        $broker->category = $request->category;
        $broker->cin_no = $request->cin_no;
        $broker->address = $request->address;
        $broker->contact_no = $request->contact_no;
        $broker->email = $request->email;
        $broker->irdia_registration_no = $request->irdia_registration_no;
        $broker->favicon_icon = $request->favicon_icon;
        $broker->logo = $request->logo;
        $broker->city = $request->city;
        $broker->state = $request->state;        
        $broker->meta_title = $request-> meta_title;
        $broker->meta_title = $request-> meta_description;
        $broker->pincode = $request->pincode;
        $result = $broker->save();
        if ($result) {
            return response()->json([
                'status' => 200,
                'return_data' => $broker,
                'message' => 'New Record Added Successfully'
            ]);
        } else{
            return response()->json([
                'status' => 200,
                'return_data' => $broker,
                'message' => 'New Record Not Added Successfully'
            ]);
        }   
    }

    public function getBrokerDetails(Request $request)
    {
        $columns = [
            'broker_id',
            'broker_name',
            'category',
            'cin_no',
            'address',
            'contact_no',
            'email',
            'irdia_registration_no',
            'favicon_icon',
            'logo',
            'front_logo',
            'city',
            'state',
            'pincode',
            'meta_title',
            'meta_description'
        ];

        $id = $request->input('id');
        if ($request->input('export', false)) {
            $headings = ['broker_id', 
                        'broker_name',  
                        'category',
                        'cin_no',
                        'address',
                        'contact_no',
                        'email',
                        'irdia_registration_no',
                        'favicon_icon',
                        'logo',
                        'front_logo',
                        'status',
                        'city',
                        'state',
                        'meta_title',
                        'meta_description',
                        'created_at',
                        'updated_at'];
            $queryColumns = ['column_name_1', 'column_name_2'];

            $export = new AllDataExport($request, Broker::class, $headings, $queryColumns);
            $filePath = 'Data/Broker_Data.xlsx';
            Excel::store($export, $filePath, 'public');
            $downloadLink = Storage::disk('public')->url($filePath);

            return response()->json([
                'status' => 200,
                'message' => 'Excel file generated successfully',
                'link' => $downloadLink,
            ]);
        }

        $user_id = Auth::user()->id;
        // if(config('partner_login')){
            $partner_upper_ids = getUserUpperHierarchy($user_id);
            if(count($partner_upper_ids))
                $ids = array_column($partner_upper_ids, 'id');
            else 
                $ids = [];

            $partner_upper_ids = array_merge($ids, [$user_id]);
        // }
        if(count($partner_upper_ids)){
            $partner = PartnerUserMapping::whereIn('user_id',$partner_upper_ids)->first();
        }

        if($partner){
            $partner->logo         = $this->makeFileUrl($partner->logo);
            $partner->favicon_icon = $this->makeFileUrl($partner->favicon_icon);
            $partner->meta_title   = 'dashboard';
            $partner->meta_description   = $partner->partner_name;
            $brokerDetails[] = $partner;
            return response()->json([
                'status' => 200,
                'return_data' => $brokerDetails,
                'message' => 'Record Found'
            ]);
        }else{
            $brokerDetails = $id ? Broker::select($columns)->find($id) : Broker::select($columns)->get();

            if ($brokerDetails) {
                // If single record, convert to an array to add URLs 
                if ($id) {
                    $brokerDetails->logo         = $this->makeFileUrl($brokerDetails->logo);
                    $brokerDetails->favicon_icon = $this->makeFileUrl($brokerDetails->favicon_icon);
                    $brokerDetails->front_logo   = $this->makeFileUrl($brokerDetails->front_logo);
                } else {
                    // For multiple records, loop through and format URLs
                    foreach ($brokerDetails as $broker) {
                        $broker->logo         = $this->makeFileUrl($broker->logo);
                        $broker->favicon_icon = $this->makeFileUrl($broker->favicon_icon);
                        $broker->front_logo   = $this->makeFileUrl($broker->front_logo);
                    }
                }
                $broker->show_back_to_ippb_button   = config('show_back_to_ippb_button') ? true : false;
                return response()->json([
                    'status' => 200,
                    'return_data' => $brokerDetails,
                    'message' => 'Record Found'
                ]);
            } else {
                return response()->json([
                    'status' => 404,
                    'return_data' => null,
                    'message' => 'No Record Found'
                ]);
            }
        }


        
    }
      
    private function makeFileUrl(?string $path)
    {
        if (!$path) {
            return null;
        }
    
        if (filter_var($path, FILTER_VALIDATE_URL)) {
            return $path;
        }
    
        $isS3 = config('dashboard_storage_disk') === 's3';
    
        if ($isS3) {
            $s3Root = trim(env('AWS_ROOT'), '/') . '/dashboard/storage/';
            return Storage::disk('s3')->temporaryUrl(
                $s3Root . $path,
                now()->addMinutes(15)
            );
        }
    
        return Storage::disk('public')->url($path);
    }


    // public function editBrokerDetails($id = null)
    // {
    //     if ($id) {
    //         $broker = Broker::find($id);
        
    //     if ($broker) {
    //         $brokerDetails = $broker->only([
    //             'broker_id',
    //             'broker_name',
    //             'category',
    //             'cin_no',
    //             'address',
    //             'contact_no',
    //             'email',
    //             'irdia_registration_no',
    //             'favicon_icon',
    //             'logo',
    //             'city',
    //             'state',
    //             'meta_title',
    //             'meta_description'
    //         ]);
            
    //         return response()->json([
    //             'status' => 200,
    //             'return_data' => $brokerDetails,
    //             'message' => 'Record Found'
    //         ]);
    //         } else {
    //             return response()->json([
    //                 'status' => 404,
    //                 'message' => 'Record Not Found'
    //             ]);
    //         }
    //     }
        
    //     return response()->json([
    //         'status' => 400,
    //         'message' => 'Invalid ID'
    //     ]);
    // }

    public function updateBrokerDetails(Request $request, int $id)
    {
        $auth = Auth::user();
        $updatePermission = "Broker Details.edit";
        if(!$auth->can($updatePermission)) {
            return response()->json([
                'status' => 403,
                'message' => 'You do not have permission to access this resource.',
            ], 403);
        }

        $validated = Validator::make($request->all(), [
            'broker_name' => 'required|string|max:255',
            'category' => 'nullable|string|max:255',
            'cin_no' => 'nullable|string|max:255',
            'address' => 'nullable|string|max:255',
            'contact_no' => 'nullable|string|max:20',
            'email' => 'nullable|email:rfc,dns|max:255',
            'irdia_registration_no' => 'nullable|string|max:255',
            'favicon_icon' => 'nullable|array', // Base64 string
            'logo' => 'nullable|array', // Base64 string
            'front_logo'=>'nullable|array',
            'city' => 'nullable|integer',
            'state' => 'nullable|integer',
            'meta_title' => 'nullable|string',
            'meta_description' => 'nullable|string'
        ]);
        if ($validated->fails()) {
            return response()->json([
                'status' => 500,
                'message' => $validated->errors()
            ], 500);
        }else{
            $broker = Broker::find($id);
            if (!$broker) {
                return response()->json([
                    'status' => 404,
                    'message' => 'Broker not found'
                ], 404);
            }
            $allowed = ['image/png', 'image/jpeg', 'image/jpg'];
            
    
            if ($request->filled('logo')) {
                $broker->logo = $this->handleBase64Image(
                    $request->logo,
                    'broker_logo',
                    $allowed
                );
            }
            
            if ($request->filled('favicon_icon')) {
                $broker->favicon_icon = $this->handleBase64Image(
                    $request->favicon_icon,
                    'broker_favicon',
                    $allowed
                );
            }
            
            if ($request->filled('front_logo')) {
                $broker->front_logo = $this->handleBase64Image(
                    $request->front_logo,
                    'front_logo',
                    $allowed
                );
            }
    
            $broker->broker_name = $request->broker_name;
            $broker->category = $request->category;
            $broker->cin_no = $request->cin_no;
            $broker->address = $request->address;
            $broker->contact_no = $request->contact_no;
            $broker->email = $request->email;
            $broker->irdia_registration_no = $request->irdia_registration_no;
            $broker->city = $request->city;
            $broker->state = $request->state;
            $broker->meta_title = $request-> meta_title;
            $broker->meta_description = $request-> meta_description;
            $broker->pincode = $request->pincode;
    
    
            $result = $broker->save();
            if ($result) {
                return response()->json([
                    'status' => 200,
                    'message' => 'Record Updated Successfully'
    
                ]);
            }
        }
        
    }

        private function modifyBase64Image($base64String)
    {
        return $base64String; 
    }

    private function storeImage($base64String, $folder, $name)
    {
        $base64String = preg_replace('/^data:image\/(png|jpg|jpeg);base64,/', '', $base64String);
        $image = base64_decode($base64String);
        $fileName = $name; 
        if (config('dashboard_storage_disk') === 's3') {
            $s3Root = trim(env('AWS_ROOT'), '/');
            $s3Path = $s3Root . '/dashboard/storage/' . $folder . '/' . $fileName;
    
            Storage::disk('s3')->put($s3Path, $image);
    
            return $folder . '/' . $fileName;
        }

        $path = storage_path('app/public/' . $folder);

        if (!file_exists($path)) {
            mkdir($path, 0755, true);
        }
        file_put_contents($path . '/' . $fileName, $image);
        return $folder  . '/' . $fileName; 
    }

    public function deleteBrokerDetails($id)
    {
        $broker = Broker::find($id);
        $result = $broker->delete();
            if ($result) {
            return response()->json([
                'status' => 200,
                'return_data' => $broker,
                'message' => ' Record Deleted Successfully'
            ]);
        }
    }

    private function handleBase64Image($image, $folder, $allowed)
    {
        if (!isset($image['image_data']) || !is_string($image['image_data'])) {
            throw new HttpResponseException( response()->json([
                'status' => 400,
                'message' => 'Image data is required',
            ], 400));
        }
        if (substr_count($image['name'] ?? '', '.') > 1) {
            throw new HttpResponseException(response()->json([
                'status' => 400,
                'message' => 'Invalid file name',
            ], 400));
        }

        $base64 = $image['image_data'];

        if (str_contains($base64, ',')) {
            $base64 = explode(',', $base64)[1];
        }

        $imageData = base64_decode($base64, true);

        if (!$imageData) {
            throw new HttpResponseException(
                response()->json([
                    'status' => 400,
                    'message' => 'Invalid base64 image data',
                ], 400)
            );
        }

        $imgInfo = getimagesizefromstring($imageData);

        if ($imgInfo === false) {
            throw new HttpResponseException( response()->json([
                'status' => 400,
                'message' => 'Not a valid image',
            ], 400));
        }

        $mime = $imgInfo['mime'];
        if (!in_array($mime, $allowed)) {
            throw new HttpResponseException( response()->json([
                'status' => 400,
                'message' => 'Invalid image type',
            ], 400));
        }

        // Clean + store
        $image['image_data'] = $this->modifyBase64Image($image['image_data']);

        $extension = explode('/', $mime)[1]; // jpeg, png, etc.
        $filename = uniqid('img_') . '_' . time() . '.' . $extension;

        return $this->storeImage(
            $image['image_data'],
            $folder,
            $filename ?? null
        );
    }

}
