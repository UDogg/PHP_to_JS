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
         Schema::create('corporate_user_whitelisting', function (Blueprint $table) {
            $table->id();
            $table->integer('corporate_id');
            $table->string('email')->nullable();
            $table->string('mobile')->nullable();
            $table->tinyInteger('status')->default(0);
            $table->integer('otp')->nullable();
            $table->timestamp('otp_sent_at')->nullable();
            $table->integer('failed_login_attempts')->default(0);
            $table->timestamp('lockout_time')->nullable();
            $table->timestamps(); 
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('corporate_user_whitelisting');
    }
};
