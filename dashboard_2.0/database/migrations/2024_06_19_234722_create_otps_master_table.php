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
        if(!Schema::hasTable('otps_master')) {

            Schema::create('otps_master', function (Blueprint $table) {
                $table->id('otp_id');
                $table->time('otp_validation_time');
                $table->time('resend_otp_time');
                $table->string('broker_name');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('otps_master');
    }
};
