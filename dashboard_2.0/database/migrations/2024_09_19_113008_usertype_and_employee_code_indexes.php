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
        //
        Schema::table('users', function (Blueprint $table) {
            $table->index('usertype')   ;
            $table->index('employee_code');
            $table->index('reportingto');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::table('users', function (Blueprint $table) {
            $table->dropIndex('users_usertype_index');
            $table->dropIndex('users_employee_code_index');
            $table->dropIndex('users_reportingto_index');
        });
    }
};
