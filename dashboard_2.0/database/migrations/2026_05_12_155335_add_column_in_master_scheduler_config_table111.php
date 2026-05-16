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
        Schema::table('master_scheduler_config', function (Blueprint $table) {
            $table->string('schedule_time')->nullable();
            $table->date('report_start_date')->nullable();
            $table->date('report_end_date')->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('master_scheduler_config', function (Blueprint $table) {
            Schema::dropIfExists('master_scheduler_config');
        });
    }
};
