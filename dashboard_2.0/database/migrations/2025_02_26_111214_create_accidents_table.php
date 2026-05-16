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
        Schema::create('accidents', function (Blueprint $table) {
            $table->id();
            $table->string('nature_of_accident')->unique();
            $table->enum('status',['Y','N'])->default('Y');
            $table->timestamps();
        });
    }                                                           

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('accidents');
    }
};
