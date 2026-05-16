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
        Schema::table('user_mappings', function (Blueprint $table) {
            $table->integer('role_id')->nullable();
            $table->integer('reportingto')->nullable(); 
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('user_mappings', function (Blueprint $table) {
            $table->dropColumn('role_id');
            $table->dropColumn('reportingto');

        });
    }
};
