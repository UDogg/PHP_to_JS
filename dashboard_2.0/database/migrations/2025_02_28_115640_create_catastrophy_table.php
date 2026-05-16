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
        Schema::create('catastrophy', function (Blueprint $table) {
            $table->id();
            $table->string('status')->nullable();
            $table->string('isOngoing')->nullable();
            $table->string('catastrophicDateValidUpto')->nullable();
            $table->string('catastrophicDate')->nullable();
            $table->string('catastrophicCode')->nullable()->default(0);
            $table->string('catastrophicName')->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('catastrophy');
    }
};
