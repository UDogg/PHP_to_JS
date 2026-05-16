<?php
namespace App\Http\Controllers\Master;

use App\Http\Controllers\Controller;
use App\Models\Menu;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Hash;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;

class MenuController extends Controller{
    public function index(Request $request){
        $menu = Menu::select('menu_id', 'menu_name', 'menu_link','menu_slug','created_at', 'updated_at')->orderBy('menu_id','desc')->latest();
        $columns = $menu;
        $menu_count = $menu->get();
        $columns = $menu;
        $menu = $menu->get();
        if(count($menu_count) != 0) {
            $columns = $menu;
            $columns = array_keys($columns->first()->toArray());
        } else {
            $columns = ['menu_name','menu_link','menu_slug','created_at','updated_at'];
        }
        foreach ($columns as $key => $value) {
            if ($value === 'menu_id') {
                unset($columns[$key]);
            } elseif ($value === 'menu_name') {
                $columns[$key] = 'Menu Name';
            } elseif ($value === 'menu_link') {
                $columns[$key] = 'Route Link';
            } else {
                $columns[$key] = str::title(str_replace('_', ' ', $value));
            }
        }
        return view('menu.index', compact('menu', 'columns'));
    }

    public function store(Request $request){
        $rules = [
            'menu_name' => ['required', 'string'],
            'menu_link' => ['required', 'url'],
            'menu_slug' => ['required', 'string'],
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{
            $menu = new Menu();
            $menu->menu_name = $request->menu_name;
            $menu->menu_link = $request->menu_link;
            $menu->menu_slug = $request->menu_slug;
            $menu->save();
            if ($menu->save()==true) {
                return redirect()->route('menu.index')->with([
                    'message' => 'Menu Created Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Creating User.',
                ])->withInput();
            }
        }
    }
    public function create()
    { 
        return view('menu.create');
    }
    public function edit(Menu $menu)
    {
        return view('menu.edit', compact('menu'));
    }
    public function update(Request $request,Menu $menu)
    {
        $rules = [
            'menu_name' => ['required', 'string'],
            'menu_link' => ['required', 'url']
        ];
        $validator = Validator::make($request->all(), $rules);
        if ($validator->fails()) {
            return redirect()->back()->withErrors($validator->errors())->withInput();
        }else{
            $menu->menu_name = $request->menu_name;
            $menu->menu_link = $request->menu_link;
            $menu->menu_slug = $menu->menu_slug;
            $menu->save();
            if ($menu->save()==true) {
                return redirect()->route('menu.index')->with([
                    'message' => 'Menu Updated Successfully.',
                    'class' => 'success',
                ]);
            } else {
                return redirect()->back()->withErrors([
                    'message' => 'Error While Updating User.',
                ])->withInput();
            }
        }
        
    }
    public function destroy(string $id)
    {
        $menu = Menu::find($id);
        if ($menu->delete()) {
            return redirect()->route('menu.index')->with([
                'message' => 'Menu Deleted Successfully.',
                'class' => 'success',
            ]);
        } else {
            return redirect()->route('menu.index')->with([
                'message' => 'Error While Deleting the Menu.',
                'class' => 'danger',
            ]);
        }
    }

}