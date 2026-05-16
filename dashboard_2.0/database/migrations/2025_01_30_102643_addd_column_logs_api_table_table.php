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
        if (Schema::hasTable('logs_api_table')) {

            Schema::table('logs_api_table', function (Blueprint $table) {
                $table->string('api_type')->nullable();
            });
        }
    }
    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('logs_api_table');
    }
};
