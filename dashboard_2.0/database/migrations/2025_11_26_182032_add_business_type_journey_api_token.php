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
        Schema::table('journey_api_token', function (Blueprint $table) {
              $table->string('business_type')->after('seller_type')->nullable();
              $table->string('business_code')->after('business_type')->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('journey_api_token', function (Blueprint $table) {
            $table->dropColumn('business_type');
            $table->dropColumn('business_code');
        });
    }
};
