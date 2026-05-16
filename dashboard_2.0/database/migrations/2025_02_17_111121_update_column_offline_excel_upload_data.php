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
        if (Schema::hasColumn('offline_excel_upload_data', 'excel_data')) {
            Schema::table('offline_excel_upload_data', function (Blueprint $table) {
                $table->longText('excel_data')->change();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasColumn('offline_excel_upload_data', 'excel_data')) {
            Schema::table('offline_excel_upload_data', function (Blueprint $table) {
                $table->text('excel_data')->change(); 
            });
        }
    }
};
