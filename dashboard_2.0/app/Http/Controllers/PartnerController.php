<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use App\Models\PartnerUserMapping;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Facades\Storage;
use Illuminate\Http\Exceptions\HttpResponseException;

class PartnerController extends Controller
{

    public function getPartnerDetails(Request $request)
    {
        $user_id = credential_decrypt($request->input('user_id'));
       
        $partnerDetails = PartnerUserMapping::where('user_id',$user_id)->first();

        if ($partnerDetails) {
            // If single record, convert to an array to add URLs 
            if ($user_id) {
                $partnerDetails->logo         = $this->makeFileUrl($partnerDetails->logo);
                $partnerDetails->favicon_icon = $this->makeFileUrl($partnerDetails->favicon_icon);
            }
            return response()->json([
                'status' => 200,
                'return_data' => $partnerDetails,
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

    public function createPartner(Request $request)
    {
        $validated = Validator::make($request->all(), [
            'partner_name' => 'required|string|max:255',
            'user_id'      => 'required|string',
            'theme_id'     => 'required|integer',
            'favicon_icon' => 'nullable',
            'logo'          => 'nullable',
            'status'        => 'required|in:Y,N',
        ]);

        if ($validated->fails()) {
            return response()->json([
                'status'  => 422,
                'message' => $validated->errors(),
            ], 422);
        }

        try {

            $allowedMimeTypes = ['image/png', 'image/jpeg', 'image/jpg'];

            $partner = PartnerUserMapping::where('user_id',credential_decrypt($request->user_id))->first() ?? new PartnerUserMapping();

            $partner->partner_name = $request->partner_name;
            $partner->user_id      = credential_decrypt($request->user_id);
            $partner->theme_id     = $request->theme_id;
            $partner->status       = $request->status;
            
            $imageFields = [
                'logo'          => 'broker_logo',
                'favicon_icon'  => 'broker_favicon',
            ];

            foreach ($imageFields as $field => $folder) {

                if ($request->filled($field) && is_array($request->$field)) {

                    $partner->$field = $this->handleBase64Image(
                        $request->$field,
                        $folder,
                        $allowedMimeTypes
                    );
                }

                elseif ($request->hasFile($field)) {

                    $file = $request->file($field);

                    $fileName = $field . '_' . time() . '.' . $file->getClientOriginalExtension();

                    $partner->$field = $file->storeAs(
                        $folder,
                        $fileName,
                        'public'
                    );
                }
            }

            $partner->save();

            return response()->json([
                'status'  => 200,
                'message' => $partner->wasRecentlyCreated
                    ? 'Partner Mapped Successfully'
                    : 'Partner Updated Successfully',
                'data'    => $partner
            ]);

        } catch (\Exception $e) {

            \Log::error('Partner Create/Update Error', [
                'error' => $e->getMessage()
            ]);

            return response()->json([
                'status'  => 500,
                'message' => 'Something went wrong',
                'error'   => $e->getMessage()
            ], 500);
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
}
