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
        Schema::create('vehicle_sub_type', function (Blueprint $table) {
            $table->id('vehicle_sub_type_id');
            $table->string('name');

            $table->unsignedBigInteger('vehicle_type_id')->nullable();

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
        Schema::table('vehicle_sub_type', function (Blueprint $table) {
            $table->dropForeign(['vehicle_type_id']);
        });

        Schema::dropIfExists('vehicle_sub_type');
    }
};
