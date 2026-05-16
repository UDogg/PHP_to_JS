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
        Schema::create('journey_api_token', function (Blueprint $table) {
            $table->id('journey_api_token_id');
            $table->string('token')->nullable();
            $table->string('seller_id');
            $table->string('seller_type');
            $table->string('encrypted_additional_data')->nullable();
            $table->string('encrypted_form_data')->nullable();
            $table->string('lob_id');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('journey_api_token');
    }
};
