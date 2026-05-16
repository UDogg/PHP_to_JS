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
            if (Schema::hasColumn('mis_report_configurator', 'key_name')) {
                $table->dropColumn('key_name');
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('mis_report_configurator', function (Blueprint $table) {
            $table->string('key_name');
        });
    }
};
