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
        Schema::table('sub_stage_master', function (Blueprint $table) {
            if(!Schema::hasColumn('config_settings', 'is_renewal'))
            {
                $table->string('is_renewal')->nullable()->after('sub_stage_name')->comment('substage only for renewal');
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('sub_stage_master', function (Blueprint $table) {
            $table->dropColumn('is_renewal');
        });
    }
};
