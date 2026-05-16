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

        if (Schema::hasTable('excel_key_master')) {
            Schema::table('excel_key_master', function (Blueprint $table) {
                $table->string('lob_id')->nullable();
            });
        }
    }
    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasTable('excel_key_master')) {
            Schema::table('excel_key_master', function (Blueprint $table) {
                $table->dropColumn('lob_id');
            });
        }
    }
};
