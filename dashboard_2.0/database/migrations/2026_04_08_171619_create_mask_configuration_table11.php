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
        Schema::create('mask_configuration_master', function (Blueprint $table) {
            $table->id();
            $table->string('module_name');
            $table->string('role');
            $table->string('usertype');
            $table->string('status')->nullable()->default('Y');
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('mask_configuration_master');
    }
};
