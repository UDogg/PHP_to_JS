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
        Schema::create('customer_vehicles', function (Blueprint $table) {
            $table->id('customer_vehicle_id');
            $table->string('vehicle_id')->nullable();
            $table->string('fuel_id')->nullable();
            $table->string('reg_no')->nullable();
            $table->string('date_of_registration')->nullable();
            $table->string('make')->nullable();
            $table->string('model')->nullable();
            $table->string('variant')->nullable();
            $table->enum('status', ['Y', 'N'])->default('Y');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('customer_vehicles');
    }
};
