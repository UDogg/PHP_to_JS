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
        Schema::create('misp_masters', function (Blueprint $table) {
            $table->id('misp_id');
            $table->string('oem_name')->nullable();
            $table->string('misp_name')->nullable();
            $table->string('misp_code')->nullable();
            $table->string('pan_number')->nullable();
            $table->string('gstin')->nullable();
            $table->string('zone')->nullable();
            $table->string('dealer_code')->nullable();
            $table->string('pin_code')->nullable();
            $table->string('city')->nullable();
            $table->string('state')->nullable();
            $table->string('mob_no')->nullable();
            $table->string('email')->nullable();
            $table->enum('status',['Y','N'])->default('Y');
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('misp_masters');
    }
};
