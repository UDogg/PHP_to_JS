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
        if(!Schema::hasTable('data_export_log'))
        {
            Schema::create('data_export_log', function (Blueprint $table) {
                $table->id();
                $table->string('userid');
                $table->string('request');
                $table->string('file');
                $table->string('source');
                $table->string('status');
                $table->timestamp('file_expiry');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('data_export_log');

    }
};
