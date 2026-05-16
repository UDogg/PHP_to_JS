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
        Schema::create('vehicle_type_ranges', function (Blueprint $table) {
            $table->id();
            $table->unsignedBigInteger('range_type_id')->nullable();
            $table->unsignedBigInteger('vehicle_type_id')->nullable();
            $table->string('range')->nullable();

            $table->timestamps();

            $table->foreign('vehicle_type_id')
                ->references('id')
                ->on('vehicle_type')
                ->onDelete('set null')
                ->onUpdate('cascade');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('vehicle_type_ranges', function (Blueprint $table) {
            $table->dropForeign(['vehicle_type_id']);
        });

        Schema::dropIfExists('vehicle_type_ranges');
    }
};
