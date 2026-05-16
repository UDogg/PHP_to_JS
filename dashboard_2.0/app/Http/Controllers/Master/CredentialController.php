<?php

namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;
use App\Models\ConfigMaster;
use App\Models\Credential;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use PSpell\Config;

class CredentialController extends Controller
{
    public function __construct()
    {
        $this->user = Auth::user();
        $permission = credential_decrypt(config('Permission.credential.view'));
        // if(!$this->user->can($permission))
        // {
        //     return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        // }
    }
    public function index(){

        $configData = ConfigMaster::select('id', 'key')->get();

        $permission = credential_decrypt(config('Permission.credential.view')); //permission fo)r
        if(!$this->user->can($permission))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }

        $perPage = 10;
        $credential = Credential::select('credential_id', 'credential_label', 'credential_key', 'credential_value', 'enviroment', 'created_at', 'updated_at')
            ->orderBy('credential_id', 'desc')
            ->paginate($perPage);

        $credential_count = Credential::count();

        $page_nos = ceil($credential_count / $perPage);

        $current_page = $credential->currentPage();

        if ($credential_count != 0) {
            $columns = array_keys($credential->first()->toArray());
        } else {
            $columns = ['credential_id', 'credential_label', 'credential_key', 'credential_value', 'enviroment', 'created_at', 'updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'credential_id') {
                unset($columns[$key]);
            } elseif ($value === 'credential_label') {
                $columns[$key] = 'Credential Label';
            } elseif ($value === 'credential_key') {
                $columns[$key] = 'Credential Key';
            } elseif ($value === 'credential_value') {
                $columns[$key] = 'Credential Value';
            } elseif ($value === 'enviroment') {
                $columns[$key] = 'Enviroment';
            } else {
                $columns[$key] = Str::title(str_replace('_', ' ', $value));
            }
        }

        foreach ($credential as $cred) {
            $cred->credential_value = credential_decrypt($cred->credential_value);
        }

        return view('credential.index', compact('columns', 'credential', 'configData', 'credential_count', 'page_nos', 'current_page'));
    }
    public function store(Request $request){
        $permission = credential_decrypt(config('Permission.credential.edit'));
        if (!$this->user->can($permission)) {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $rules = [
            'configs' => ['required', 'integer'],
            'credential_label' => ['required', 'string'],
            'credential_key' => ['required', 'string'],
//            'credential_value' => ['required', 'string'],
            'enviroment' => ['required', 'string'],
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{

            $credential = new Credential();
            $key = env('APP_KEY');
            $credential->credential_label = $request->credential_label;
            $credential->credential_key = $request->credential_key;
            $credential->credential_value = credential_encrypt($request->credential_value) ?? '';
            $credential->enviroment = $request->enviroment;
            $credential->configuration = $request->configs;
            $credential->save();
            if ($credential->save()==true) {
                return redirect()->route('credential.index')->with([
                    'message' => 'Credential Created Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating Credential.',
                ])->withInput();
            }
        }
    }
    public function create()
    {
        $permission = credential_decrypt(config('Permission.credential.edit'));
        if (!$this->user->can($permission)) {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $all_configurations = ConfigMaster::select('key','id')->get()->all();
        return view('credential.create',compact('all_configurations'));
    }

    public function update(Request $request,Credential $credential)
    {
        $permission = credential_decrypt(config('Permission.credential.edit','No Permission'));
        if (!$this->user->can($permission)) {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $rules = [
            'credential_key' => ['required', 'string'],
            'credential_value' => ['required', 'string'],
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{
            //$key = env('APP_KEY');
            $credential->credential_label = $request->credential_label;
            $credential->credential_key = $request->credential_key;
            $credential->credential_value = credential_encrypt($request->credential_value);
            $credential->configuration = $request->credential_config;
            $credential->enviroment = $request->enviroment;
//            $credential->status = $request->status;
            $credential->save();
            if ($credential->save()==true) {
                return redirect()->route('credential.index')->with([
                    'message' => 'Credential Updated Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Updating Credential.',
                ])->withInput();
            }
        }

    }

    public function edit(Credential $credential)
    {
        $permission = credential_decrypt(config('Permission.credential.edit','No Permission'));
        if (!$this->user->can($permission)) {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $all_configurations = ConfigMaster::select('key','id')->get()->all();
        return view('credential.edit', compact('credential', 'all_configurations'));
    }

    public function destroy(Credential $credential)
    {
        $permission = credential_decrypt(config('Permission.credential.delete'));
    
        if (!$this->user->can($permission)) {
            return redirect()->route('credential.index')->with([
                'message' => 'Access Denied',
                'class' => 'danger',
            ]);
        }
    
        if ($credential->delete()) {
            return redirect()->route('credential.index')->with([
                'message' => 'Credential deleted successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('credential.index')->with([
                'message' => 'Error while deleting the credential.',
                'class' => 'danger',
            ]);
        }
    }
    
    public function AddConfig(Request $request)
    {
        $request->validate([
            'credential_config' => 'required|string|max:255|unique:configmaster,key',
        ]);
        $add_config = ConfigMaster::create([
            'key' => $request->credential_config,
        ]);
        if($add_config){
            return response()->json(['status' => 200, 'message' => 'Credential Config Added successfully']);
        }
        else{
            return response()->json(['status' => 503, 'message' => 'Something went wrong']);
        }
    }
    public function show()
    {

        $permissionGroup = DB::table('ConfigMaster')->where('key', 'Permissions')->pluck('id')[0];
        $credential = Credential::select('credential_id as id','credential_key as name')->where('configuration',$permissionGroup)->where('credential_value','')->get();
        return requestResponseMessage(['status' => 200, 'data' => $credential]);
    }

    public function filter(Request $request)
    {
        $selectedConfigId = $request->input('config_id');
        $searchQuery = $request->input('search');
        $perPage = 10;

        $query = DB::table('config_settings')
            ->join('ConfigMaster', 'ConfigMaster.id', '=', 'config_settings.configuration')
            ->select('config_settings.*');

        if (!empty($selectedConfigId)) {
            $query->where('ConfigMaster.id', $selectedConfigId);
        }

        if (!empty($searchQuery)) {
            $query->where(function ($q) use ($searchQuery) {
                $q->where('config_settings.credential_label', 'LIKE', '%' . $searchQuery . '%')
                ->orWhere('config_settings.credential_key', 'LIKE', '%' . $searchQuery . '%');
            });
        }

        $filteredCredentials = $query->paginate($perPage);

        foreach ($filteredCredentials as $cred) {
            $cred->credential_value = credential_decrypt($cred->credential_value);
        }

        return response()->json([
            'filteredCredentials' => $filteredCredentials->items(), 
            'total' => $filteredCredentials->total(),
            'current_page' => $filteredCredentials->currentPage(),
            'last_page' => $filteredCredentials->lastPage(),
            'per_page' => $filteredCredentials->perPage(),
        ]);
    }



//     public function filter(Request $request)
// {
//     $selectedConfigId = $request->input('config_id');
//         $searchQuery = $request->input('search');
//     $perPage = 10;

//         $query = DB::table('config_settings')
//             ->join('ConfigMaster', 'ConfigMaster.id', '=', 'config_settings.configuration')
//             ->select('config_settings.*');

//         if (!empty($selectedConfigId)) {
//             $query->where('ConfigMaster.id', $selectedConfigId);
//         }

//         if (!empty($searchQuery)) {
//             $query->where(function ($q) use ($searchQuery) {
//                 $q->orWhere('config_settings.credential_label', 'LIKE', '%' . $searchQuery . '%')
//                 ->orWhere('config_settings.credential_key', 'LIKE', '%' . $searchQuery . '%');
//             });
//         }

//         $filteredCredentials = $query->paginate($perPage);

//     foreach ($filteredCredentials as $cred) {
//         $cred->credential_value = credential_decrypt($cred->credential_value);
//     }
//     return response()->json([
//         'filteredCredentials' => $filteredCredentials->items(),
//         'total' => $filteredCredentials->total(),
//         'current_page' => $filteredCredentials->currentPage(),
//         'last_page' => $filteredCredentials->lastPage(),
//         'per_page' => $filteredCredentials->perPage(),
//     ]);
// }





}
