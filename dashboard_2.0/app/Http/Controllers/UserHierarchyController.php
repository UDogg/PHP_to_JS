<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;

use App\Models\User;

class UserHierarchyController extends Controller
{
    public function show(Request $request)
    {
        $request->validate([
            'id' => 'required|integer|exists:users,id'
        ]);
        $id = $request->input('id');
        $user = User::select('id', 'username', 'path', 'name', 'email', 'mobile', 'usertype','old_user_id')
            ->findOrFail($id);

        if (empty($user->path)) {
            return response()->json([
                'error' => 'Hierarchy path not generated for this user',
                'user' => $user
            ], 422);
        }

        $pathIds = array_filter(explode('/', $user->path));

       
        $upper = User::whereIn('id', $pathIds)
            ->select('id', 'username', 'path', 'name', 'email', 'mobile', 'usertype', 'old_user_id')
            ->orderByRaw(
                "FIELD(id, " . implode(',', $pathIds) . ")"
            )
            ->get();

        
        $lower = User::descendantsOf($user)
            ->select('id', 'username', 'path', 'name', 'email', 'mobile', 'usertype', 'old_user_id')
            ->orderBy('path')
            ->get();

        return response()->json([
            'user' => $user,
            'upper_hierarchy' => $upper,
            'lower_hierarchy' => $lower,
        ]);
    }
}
