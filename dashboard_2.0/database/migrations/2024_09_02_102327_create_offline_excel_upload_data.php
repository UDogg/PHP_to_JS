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
        Schema::create('offline_excel_upload_data', function (Blueprint $table) {
            $table->id('offline_excel_upload_data_id');
            $table->string('excel_file_name');
            $table->string('excel_data');
            $table->string('total_record')->nullable();
            $table->string('failed_record')->nullable();
            $table->string('success_record')->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('offline_excel_upload_data');
    }
};
