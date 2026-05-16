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
        Schema::table('excel_key_master', function (Blueprint $table) {
            if (!Schema::hasColumn('excel_key_master', 'is_visible')) {
                $table->string('is_visible')->nullable();
            } else {
                $table->string('is_visible')->nullable()->change(); 
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('excel_key_master', function (Blueprint $table) {
            if (Schema::hasColumn('excel_key_master', 'is_visible')) {
                $table->dropColumn('is_visible');
            }
        });
    }
};
