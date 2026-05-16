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
        Schema::table('mis_report_configurator', function (Blueprint $table) {
            $table->string('user_id')->nullable();
            $table->string('user_type')->nullable();
            $table->string('stage_name')->nullable();
        });
    }
    public function down(): void
    {
        Schema::table('mis_report_configurator', function (Blueprint $table) {
            $table->dropColumn('user_id');
            $table->dropColumn('user_type');
            $table->dropColumn('stage_name');
        });
    }
};
