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
        Schema::create('user_sp_details', function (Blueprint $table) {
            $table->id();
            $table->unsignedBigInteger('user_id');
            $table->foreign('user_id')->references('id')->on('users')->onDelete('cascade');
            $table->string('is_sp')->nullable();
            $table->string('sp_name')->nullable();
            $table->string('sp_urnno')->nullable();
            $table->string('sp_code')->nullable();
            $table->string('sp_type')->nullable();
            $table->string('noc_issued')->nullable();
            $table->string('sp_certificate_date')->nullable();
            $table->string('certificate_valid_from')->nullable();
            $table->string('certificate_valid_till')->nullable();
            $table->char('status')->default('Y');
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('user_sp_details');
    }
};
