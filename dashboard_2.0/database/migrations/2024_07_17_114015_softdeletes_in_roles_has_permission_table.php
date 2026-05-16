<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('role_has_permissions', function (Blueprint $table) {
            //
            if(!Schema::hasColumn('role_has_permissions', 'deleted_at')) {
                $table->softDeletes();
            }
            if(!Schema::hasColumn('roles_has_permission', 'created_at')) {
                $table->timestamps();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('roles_has_permissions', function (Blueprint $table) {
            //
            Schema::dropColumns('role_has_permissions','deleted_at');
            Schema::dropColumns('role_has_permissions','created_at');
            Schema::dropColumns('role_has_permissions','updated_at');
        });
    }
};
