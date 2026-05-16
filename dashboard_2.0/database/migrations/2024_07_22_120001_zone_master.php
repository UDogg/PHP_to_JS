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
        if(!Schema::hasTable('zone_master')) {

            Schema::create('zone_master', function (Blueprint $table) {
                $table->id('id');
                $table->string('office_zone');
                $table->string('office_name');
                $table->string('parent_office');
                $table->string('office_pincode');
                $table->string('contact_phone');
                $table->string('contact_email');
                $table->string('address');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('zone_master');
        
    }
};
