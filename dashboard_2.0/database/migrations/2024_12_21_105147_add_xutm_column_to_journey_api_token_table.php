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
        if (Schema::hasTable('journey_api_token')) {
            if (!Schema::hasColumn('journey_api_token', 'xutm')) {
                Schema::table('journey_api_token', function (Blueprint $table) {
                    $table->string('xutm')->nullable()->after('lob_id');
                });
            }
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasTable('journey_api_token') && Schema::hasColumn('journey_api_token', 'xutm')) {
            Schema::table('journey_api_token', function (Blueprint $table) {
                $table->dropColumn('xutm');
            });
        }
    }
};
