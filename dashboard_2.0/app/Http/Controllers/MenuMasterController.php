<?php

namespace App\Http\Controllers;

use App\Http\Requests\createSubChildMenu;
use App\Http\Requests\createSubMenu;
use App\Models\MenuMasterModel;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Spatie\Permission\Models\Permission;

class MenuMasterController extends Controller
{
    //
    public function __construct(Auth $auth)
    {
        $this->auth = $auth::user();
        if(!$this->auth->can('menu.view'))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
    }
    public function index()
    {

        return view('MenuMaster');
    }
    public function createMenu(Request $request)
    {
        $validate = $request->validate([
            'menu' => ['required','string','unique:MenuMaster,menu'],
            'IsChild' => ['required','string','in:Y,N'],
            'IsFrontEndMainMenu' => ['required','string','in:Y,N'],
            'order_by' =>['required'],

        //            'route' => ['required','string'],
        ]);
        if(!$this->auth->can('menu.edit'))
        {
           return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }

        $duplicateCheck = MenuMasterModel::where('menu',$request->menu)->where('deleted_at','')->first();
        if(!empty($duplicateCheck))
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Already Exist'
            ]);
        }
        $exists = MenuMasterModel::where('order_by', $request->order_by)->exists();
        if ($exists) {
            MenuMasterModel::where('order_by', '>=', $request->order_by)
                ->increment('order_by');
        }
        $menuCreate = MenuMasterModel::create([
            'menu' => $request->menu,
            'route' => $request->route,
            'icon' => $request->icon,
            'is_child' => $request->IsChild,
            'isFrontEnd' => $request->IsFrontEndMainMenu ?? 'N',
            'front_end_url' => $request->FrontendUrlMainMenu ?? null,
            'order_by' => $request->order_by
        ]);
        if($menuCreate)
        {
            $arrartypes = ['edit','view','delete','upload'];
            foreach ($arrartypes as $key => $value)
            {
                $permission = Permission::create(['name' => $request->menu.'.'.$value,'guard_name' => 'sanctum']);
            }
            return response()->json([
                'status' => 200,
                'message' => 'Menu Created Successfully'
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Creation Failed'
            ]);
        }

    }
    public function createSubMenu(createSubMenu $request)
    {
        if(!$this->auth->can('menu.edit'))
        {
            return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $SubMenu = MenuMasterModel::create([
            'menu' => $request->subMenuName,
            'menuId' => $request->menu_nm,
            'route' => $request->route ?? null,
            'icon' => $request->icon ?? null,
            'front_end_url' => $request->f_url ?? null,
            'isFrontEnd' => $request->isFrontEnd ?? 'N',
        ]);
        if($SubMenu)
        {
        $arr_writes = ['edit','view','delete','upload'];
        foreach ($arr_writes as $key => $value)
        {
            $permission = Permission::create(['name' => $request->subMenuName.'.'.$value]);
        }
            return response()->json([
                'status' => 200,
                'message' => 'Menu Created Successfully'
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Creation Failed'
            ]);
        }
    }
    public function CreateSubChildMenu(createSubChildMenu $request)
    {
//        check for edit permission

        if(!$this->auth->can('menu.edit'))
        {
           return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $SubMenu = MenuMasterModel::create([
            'menu' => $request->subMenuName,
            'subMenuId' => $request->menu_nm,
            'route' => $request->route ?? null,
            'icon' => $request->icon ?? null,
        ]);
        if($SubMenu)
        {
            return response()->json([
                'status' => 200,
                'message' => 'Menu Created Successfully'
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Creation Failed'
            ]);
        }
    }
    public function getMenu()
    {
        $MainMenu = MenuMasterModel::select('id', 'menu','route' , 'status', 'icon', 'front_end_url', 'is_child', 'isFrontEnd','order_by')
            ->orderBy('order_by','ASC')
            ->get();
        if ($MainMenu->isNotEmpty()) {
            $Submenu = MenuMasterModel::select('id', 'menu', 'menuId','route','icon')
                ->where('menuId', '!=', null)
                ->get()
                ->groupBy('menuId');

            $MainMenu = $MainMenu->map(function($menu) use ($Submenu) {
                $menu->submenus = $Submenu->get($menu->id) ?: [];
                return $menu;
            });

            return response()->json([
                'status' => 200,
                'data' => $MainMenu,
                'message' => "Menu List",
            ],200);
        } else {
            return response()->json([
                'status' => 500,
                'data'=> [],
                'message' => 'Menu Not Found'
            ],500);
        }
    }
    public function getSubMenu()
    {
        $Submenu = MenuMasterModel::select('id','menu','menuId')->where('menuId','!=',null)->get()->all();
        if(!empty($Submenu))
        {
            return response()->json([
                'status' => 200,
                'data' => $Submenu
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Not Found'
            ]);
        }
    }
    public function getChildSubMenu()
    {
        $Submenu = MenuMasterModel::select('id','menu','subMenuId')->where('subMenuId','!=',null)->get()->all();
        if(!empty($Submenu))
        {
            return response()->json([
                'status' => 200,
                'data' => $Submenu
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Not Found'
            ]);
        }
    }
    public function deleteMenu(Request $request)
    {
        $validate = $request->validate([

            'id' => ['required', 'int']
        ]);
        $id = $request->id;
        if(!$this->auth->can('menu.delete'))
        {
           return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $deleteMainMenu = MenuMasterModel::where('id',$id)->delete();
        $deleteSubMenu = MenuMasterModel::where('menuId',$id)->delete();
        $deleteSubMenuChild = MenuMasterModel::where('subMenuId',$id)->delete();
        if($deleteMainMenu)
        {
            return response()->json([
                'status' => 200,
                'message' => 'Menu Deleted Successfully'
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Menu Deletion Failed'
            ]);
        }
    }
    public function deleteSubMenu(Request $request)
    {
        $validate = $request->validate([
            'id' => ['required', 'int']
        ]);
        $id = $request->id;
        if(!$this->auth->can('menu.delete'))
        {
           return  requestResponseMessage(['status' => 404,'message'=>'Access Denied']);
        }
        $deleteSubMenu = MenuMasterModel::where('id',$id)->get()->toArray();
        $memuName = $deleteSubMenu[0]['menu'];

        $deleteSubMenu = MenuMasterModel::where('id',$id)->forceDelete();
        $MenuPermissions = [$memuName.'.edit',$memuName.'.view',$memuName.'.delete',$memuName.'.upload'];
        $deleteMenuPermissions = Permission::whereIn('name',$MenuPermissions)->delete();

        if($deleteSubMenu)
        {
            return response()->json([
                'status' => 200,
                'message' => 'Data Deleted Successfully'
            ]);
        }
        else
        {
            return response()->json([
                'status' => 404,
                'message' => 'Data Deletion Failed'
            ]);
        }
    }

    public function updateSubMenu(Request $request)
    {
        if (!$this->auth->can('menu.edit')) {
            return response()->json(['status' => 404, 'message' => 'Access Denied']);
        }
        $id = $request->id ?? '';
        $menu = $request->menu ?? '';
        $route = $request->route ?? '';
        $icon = $request->icon ?? '';
        $status = $request->status ?? '';
        $url = $request->url ?? '';
        $is_frontend = $request->is_frontend ?? '';
        $is_child = $request->is_child ?? '';
        $order_by = $request->order_by === '' ? null : $request->order_by;

        if (!is_null($order_by)) {
            $exists = MenuMasterModel::where('order_by', $order_by)
                ->where('id', '!=', $id)
                ->exists();

            if ($exists) {
                MenuMasterModel::where('order_by', '>=', $order_by)
                    ->where('id', '!=', $id)
                    ->increment('order_by');
            }
        }

        $update = MenuMasterModel::where('id', $id)->update([
            'menu' => $menu,
            'route' => $route,
            'icon' => $icon,
            'status' => $status,
            'front_end_url' => $url,
            'is_child' => $is_child,
            'isFrontEnd' => $is_frontend,
            'order_by' => $order_by,
        ]);

        if ($update) {
            return response()->json([
                'status' => 200,
                'message' => 'Data Updated Successfully',
            ]);
        } else {
            return response()->json([
                'status' => 404,
                'message' => 'Data Updation Failed',
            ]);
        }
    }

}

