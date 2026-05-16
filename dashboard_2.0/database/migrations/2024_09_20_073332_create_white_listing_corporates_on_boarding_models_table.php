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
        Schema::create('white_listing_corporates_on_boarding_master', function (Blueprint $table) {
            $table->id();
            $table->string('corporates_on_boarding_id');
            $table->string('email_id');
            $table->string('mobile_no', 15); 
            $table->enum('status', ['Active', 'Inactive']);
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('white_listing_corporates_on_boarding_master');
    }
};
