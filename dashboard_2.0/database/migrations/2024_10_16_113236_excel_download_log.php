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
        if(!Schema::hasTable('excel_download_log'))
        {
            Schema::create('excel_download_log', function (Blueprint $table) {
                $table->id();
                $table->integer('user_id');
                $table->string('file_name')->nullable();
                $table->string('source')->nullable();
                $table->string('status')->nullable()->default(0);
                $table->json('request')->nullable();
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('excel_download_log');
    }
};
