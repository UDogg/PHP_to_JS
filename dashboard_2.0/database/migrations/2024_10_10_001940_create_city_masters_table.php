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
        if(!Schema::hasTable('city_masters'))
        {
            Schema::create('city_masters', function (Blueprint $table) {
                $table->id('city_id');
                $table->integer('zone_id')->nullable();
                $table->integer('state_id')->nullable();
                $table->string('city_name')->nullable();
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
        Schema::dropIfExists('city_masters');
    }
};
