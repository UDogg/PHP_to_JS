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
        Schema::table('offline_excel_upload_data', function (Blueprint $table) {
            $table->integer('lob_id')->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('offline_excel_upload_data', function (Blueprint $table) {
            $table->dropColumn('lob_id');
        });
    }
};
