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
        Schema::create('role_pi_data_mapping', function (Blueprint $table) {
            $table->id();
            $table->string('module_id')->nullable();
            $table->string('field_name')->nullable();
            $table->string('is_enabled')->nullable()->default('N');
            $table->string('mask_type')->nullable();
            $table->string('mask_scope')->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('role_pi_data_mapping');
    }
};
