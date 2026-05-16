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
        Schema::table('sms_template', function (Blueprint $table) {
            if (!Schema::hasColumn('sms_template', 'dlt_id')) {
                $table->string('dlt_id')->nullable();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('sms_template', function (Blueprint $table) {
            if (Schema::hasColumn('sms_template', 'dlt_id')) {
                $table->dropColumn('dlt_id');
            }
        });
    }
};
