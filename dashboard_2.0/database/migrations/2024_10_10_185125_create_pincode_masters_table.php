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
        if(!Schema::hasTable('pincode_masters'))
        {
            Schema::create('pincode_masters', function (Blueprint $table) {
                $table->id('pincode_id');
                $table->string('pincode')->nullable();
                $table->string('country_code')->nullable();
                $table->string('state_id')->nullable();
                $table->string('city_id')->nullable();
                $table->string('area')->nullable();
                $table->string('latitude')->nullable();
                $table->string('longitude')->nullable();
                $table->string('geospatial_accuracy')->nullable();
                $table->string('sequence')->nullable();
                $table->timestamps();
                $table->softDeletes();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('pincode_masters');
    }
};
