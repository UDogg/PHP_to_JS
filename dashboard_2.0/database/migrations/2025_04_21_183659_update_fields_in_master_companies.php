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
        Schema::table('master_companies', function (Blueprint $table) {
            $table->enum('live_insu_company', ['Y', 'N'])->default('Y')->after('logo');
            $table->dropColumn(['health_alias', 'motor_alias', 'url', 'is_renewal', 'is_renewal_bike']);
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('master_companies', function (Blueprint $table) {
            $table->string('health_alias')->nullable();
            $table->string('motor_alias')->nullable();
            $table->string('url')->nullable();
            $table->boolean('is_renewal')->default(false);
            $table->boolean('is_renewal_bike')->default(false);

            $table->dropColumn('live_insu_company');
        });
    }
};
