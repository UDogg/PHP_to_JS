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
        Schema::table('oem_masters', function (Blueprint $table) {
            $table->string('misp_name')->nullable();
            $table->string('pan_number')->nullable();
            $table->string('gstin')->nullable();
            $table->string('zone')->nullable();
            $table->string('dealer_code')->nullable();
            $table->string('branch_name')->nullable();
            $table->string('address')->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('oem_masters', function (Blueprint $table) {
            //
        });
    }
};
