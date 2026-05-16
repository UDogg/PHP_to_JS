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
        Schema::table('data_export_log', function (Blueprint $table) {
            if (!Schema::hasColumn('data_export_log', 'request')) {
                $table->string('request')->nullable();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('data_export_log', function (Blueprint $table) {
            if (Schema::hasColumn('data_export_log', 'request')) {
                $table->dropColumn('request');
            }
        });
    
    }
};
